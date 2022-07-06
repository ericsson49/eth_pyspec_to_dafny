include "ssz.dfy"
include "simpletypes.dfy"
include "classes.dfy"
include "consts.dfy"

import opened SSZ
import opened SimpleTypes
import opened Classes
import opened Consts

function method get_current_epoch(state: BeaconState): Epoch
function method is_slashable_attestation_data(data1: AttestationData, data2: AttestationData): bool
function method is_valid_indexed_attestation(state: BeaconState, attestation: IndexedAttestation): bool
function method get_indexed_attestation(state: BeaconState, attestation: Attestation): IndexedAttestation
function method get_active_validator_indices(state: BeaconState, epoch: Epoch): Sequence<ValidatorIndex>
function method get_total_active_balance(state: BeaconState): Gwei
method process_slots(state: BeaconState, slot: Slot) returns (status_: Status)
method state_transition(state: BeaconState, block: SignedBeaconBlock, check: bool) returns (status_: Status)

/*
    Return the epoch number at ``slot``.
    */
function method compute_epoch_at_slot(slot: Slot): Epoch
{
  Epoch_new(slot / SLOTS_PER_EPOCH)
}

/*
    Return the start slot of ``epoch``.
    */
function method compute_start_slot_at_epoch(epoch: Epoch): Slot
{
  Slot_new(epoch * SLOTS_PER_EPOCH)
}

method get_forkchoice_store(anchor_state: BeaconState, anchor_block: BeaconBlock)
returns (status_: Status, ret_: Store)
{
  :- pyassert(anchor_block.state_root == hash_tree_root(anchor_state));
  var anchor_root: Root := Root_new(hash_tree_root(anchor_block));
  var anchor_epoch: Epoch := get_current_epoch(anchor_state);
  var justified_checkpoint: Checkpoint := Checkpoint(anchor_epoch, anchor_root);
  var finalized_checkpoint: Checkpoint := Checkpoint(anchor_epoch, anchor_root);
  var proposer_boost_root: Root := Root_new(0);
  var tmp_0 := new Store.Init(uint64_new(anchor_state.genesis_time + (SECONDS_PER_SLOT * anchor_state.slot)), anchor_state.genesis_time, justified_checkpoint, finalized_checkpoint, justified_checkpoint, proposer_boost_root, Set_new([]), Dict_new([(anchor_root, anchor_block.copy())]), Dict_new([(anchor_root, anchor_state.copy())]), Dict_new([(justified_checkpoint, anchor_state.copy())]), Dict_new([]));
  return Success, tmp_0;
}

function method get_slots_since_genesis(store: Store): int
{
  (store.time - store.genesis_time) / SECONDS_PER_SLOT
}

function method get_current_slot(store: Store): Slot
{
  Slot_new(GENESIS_SLOT + get_slots_since_genesis(store))
}

function method compute_slots_since_epoch_start(slot: Slot): int
{
  slot - compute_start_slot_at_epoch(compute_epoch_at_slot(slot))
}

function method get_ancestor(store: Store, root: Root, slot: Slot): (Status, Root)
{
  var tmp_0 := store.blocks.get(root);
  if tmp_0.0.IsFailure() then
    (Failure, Root_default)
  else
    var block: BeaconBlock := tmp_0.1;
    if block.slot > slot then
      get_ancestor(store, block.parent_root, slot)
    else
      if block.slot == slot then
        (Success, root)
      else
        (Success, root)
}

function method get_latest_attesting_balance(store: Store, root: Root): (Status, Gwei) 
{
  var tmp_0 := store.checkpoint_states.get(store.justified_checkpoint);
  if tmp_0.0.IsFailure() then
    (Failure, Gwei_default)
  else
    var state: BeaconState := tmp_0.1;
    var active_indices: Sequence<ValidatorIndex> := get_active_validator_indices(state, get_current_epoch(state));
    var attestation_score: Gwei := Gwei_new(sum(pymap((i) => state.validators.get(i).effective_balance, filter((i) => store.latest_messages.contains(i) && !store.equivocating_indices.contains(i) && get_ancestor(store, store.latest_messages.get(i).root, store.blocks.get(root).slot) == root, active_indices))));
    if store.proposer_boost_root == Root_new(0) then
      (Success, attestation_score)
    else
      var proposer_score: Gwei := Gwei_new(0);
      var tmp_1 := store.blocks.get(root);
      if tmp_1.0.IsFailure() then
        (Failure, Gwei_default)
      else
        var tmp_2 := get_ancestor(store, store.proposer_boost_root, tmp_1.1.slot);
        if tmp_2.0.IsFailure() then
          (Failure, Gwei_default)
        else
          var proposer_score_2: Gwei :=
            if tmp_2.1 == root then
              var num_validators: int := len(get_active_validator_indices(state, get_current_epoch(state)));
              var avg_balance: Gwei := get_total_active_balance(state) / num_validators;
              var committee_size: uint64 := num_validators / SLOTS_PER_EPOCH;
              var committee_weight: Gwei := committee_size * avg_balance;
              var proposer_score_1: Gwei := committee_weight * PROPOSER_SCORE_BOOST / 100;
              proposer_score_1
            else
              proposer_score;
          (Success, attestation_score + proposer_score_2)
}

method filter_block_tree(store: Store, block_root: Root, blocks: Dict<Root,BeaconBlock>)
returns (status_: Status, ret_: bool) 
{
  var block: BeaconBlock :- a_(store.blocks.get(block_root));
  var children: PyList<Root> := pylist(filter((root) => store.blocks.get_nf(root).parent_root == block_root, store.blocks.keys()));
  if any(children) {
    var tmp_0 := iter(children);
    var tmp_1 := PyList_new([]);
    while has_next(tmp_0) {
      var child := next(tmp_0);
      var tmp_2 :- filter_block_tree(store, child, blocks);
      tmp_1.append(tmp_2);
    }
    var filter_block_tree_result: PyList<bool> := pylist(tmp_1);
    if any(filter_block_tree_result) {
      blocks.set_value(block_root, block);
      return Success, true;
    }
    return Success, false;
  }
  var head_state: BeaconState :- a_(store.block_states.get(block_root));
  var correct_justified: bool := if (store.justified_checkpoint.epoch == GENESIS_EPOCH) then true else head_state.current_justified_checkpoint == store.justified_checkpoint;
  var correct_finalized: bool := if (store.finalized_checkpoint.epoch == GENESIS_EPOCH) then true else head_state.finalized_checkpoint == store.finalized_checkpoint;
  if if (correct_justified) then correct_finalized else false {
    blocks.set_value(block_root, block);
    return Success, true;
  }
  return Success, false;
}

/*
    Retrieve a filtered block tree from ``store``, only returning branches
    whose leaf state's justified/finalized info agrees with that in ``store``.
    */
method get_filtered_block_tree(store: Store)
returns (status_: Status, ret_: Dict<Root,BeaconBlock>) 
{
  var base: Root := store.justified_checkpoint.root;
  var blocks: Dict<Root,BeaconBlock> := Dict_new([]);
  var a, b := filter_block_tree(store, base, blocks);
  return Success, blocks;
}

method get_head(store: Store)
returns (status_: Status, ret_: Root) 
{
  var blocks: Dict<Root,BeaconBlock> :- get_filtered_block_tree(store);
  var head: Root := store.justified_checkpoint.root;
  var head_2 := head;
  while true {
    var children: PyList<Root> := pylist(filter((root) => blocks.get_nf(root).parent_root == head_2, blocks.keys()));
    if len(children) == 0 {
      return Success, head_2;
    }
    var head_1: Root :- a_(max_f(children, (root: Root) => var tmp_0 := get_latest_attesting_balance(store, root); if (tmp_0.0.IsFailure()) then (Failure, (Gwei_default, Root_default)) else (Success, (tmp_0.1, root))));
    head_2 := head_1;
  }
}

/*
    To address the bouncing attack, only update conflicting justified
    checkpoints in the fork choice if in the early slots of the epoch.
    Otherwise, delay incorporation of new justified checkpoint until next epoch boundary.

    See https://ethresear.ch/t/prevention-of-bouncing-attack-on-ffg/6114 for more detailed analysis and discussion.
    */
method should_update_justified_checkpoint(store: Store, new_justified_checkpoint: Checkpoint)
returns (status_: Status, ret_: bool) 
{
  if compute_slots_since_epoch_start(get_current_slot(store)) < SAFE_SLOTS_TO_UPDATE_JUSTIFIED {
    return Success, true;
  }
  var justified_slot: Slot := compute_start_slot_at_epoch(store.justified_checkpoint.epoch);
  var tmp_0 :- a_(get_ancestor(store, new_justified_checkpoint.root, justified_slot));
  if !(tmp_0 == store.justified_checkpoint.root) {
    return Success, false;
  }
  return Success, true;
}

method validate_target_epoch_against_current_time(store: Store, attestation: Attestation)
returns (status_: Status) 
{
  var target: Checkpoint := attestation.data.target;
  var current_epoch: Epoch := compute_epoch_at_slot(get_current_slot(store));
  var previous_epoch: Epoch := if (current_epoch > GENESIS_EPOCH) then current_epoch - 1 else GENESIS_EPOCH;
  :- pyassert(PyList_new([current_epoch, previous_epoch]).contains(target.epoch));
}

method validate_on_attestation(store: Store, attestation: Attestation, is_from_block: bool)
returns (status_: Status) 
{
  var target: Checkpoint := attestation.data.target;
  if !is_from_block {
    :- validate_target_epoch_against_current_time(store, attestation);
  }
  :- pyassert(target.epoch == compute_epoch_at_slot(attestation.data.slot));
  :- pyassert(store.blocks.contains(target.root));
  :- pyassert(store.blocks.contains(attestation.data.beacon_block_root));
  :- pyassert(store.blocks.get_nf(attestation.data.beacon_block_root).slot <= attestation.data.slot);
  var target_slot: Slot := compute_start_slot_at_epoch(target.epoch);
  var tmp_0 :- a_(get_ancestor(store, attestation.data.beacon_block_root, target_slot));
  :- pyassert(target.root == tmp_0);
  :- pyassert(get_current_slot(store) >= (attestation.data.slot + 1));
}

method store_target_checkpoint_state(store: Store, target: Checkpoint)
returns (status_: Status) 
{
  if !store.checkpoint_states.contains(target) {
    var tmp_0 :- a_(store.block_states.get(target.root));
    var base_state: BeaconState := tmp_0.copy();
    if base_state.slot < compute_start_slot_at_epoch(target.epoch) {
      :- process_slots(base_state, compute_start_slot_at_epoch(target.epoch));
    }
    store.checkpoint_states.set_value(target, base_state);
  }
}

method update_latest_messages(store: Store, attesting_indices: Sequence<ValidatorIndex>, attestation: Attestation)
{
  var target: Checkpoint := attestation.data.target;
  var beacon_block_root: Root := attestation.data.beacon_block_root;
  var non_equivocating_attesting_indices: PyList<ValidatorIndex> := pylist(pymap((i) => i, filter((i) => !store.equivocating_indices.contains(i), attesting_indices)));
  var tmp_for_0: Iterator<ValidatorIndex> := iter(non_equivocating_attesting_indices);
  while has_next(tmp_for_0) {
    var i: ValidatorIndex := next(tmp_for_0);
    if !store.latest_messages.contains(i) || target.epoch > store.latest_messages.get_nf(i).epoch {
      store.latest_messages.set_value(i, LatestMessage(target.epoch, beacon_block_root));
    }
  }
}

method on_tick(store: Store, time: uint64)
returns (status_: Status) 
{
  var previous_slot: Slot := get_current_slot(store);
  store.time := time;
  var current_slot: Slot := get_current_slot(store);
  if current_slot > previous_slot {
    store.proposer_boost_root := Root_new(0);
  }
  if !if (current_slot > previous_slot) then compute_slots_since_epoch_start(current_slot) == 0 else false {
    return;
  }
  if store.best_justified_checkpoint.epoch > store.justified_checkpoint.epoch {
    var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
    var ancestor_at_finalized_slot: Root :- a_(get_ancestor(store, store.best_justified_checkpoint.root, finalized_slot));
    if ancestor_at_finalized_slot == store.finalized_checkpoint.root {
      store.justified_checkpoint := store.best_justified_checkpoint;
    }
  }
}

method on_block(store: Store, signed_block: SignedBeaconBlock)
returns (status_: Status) 
{
  var block: BeaconBlock := signed_block.message;
  :- pyassert(store.block_states.contains(block.parent_root));
  var tmp_0 :- a_(store.block_states.get(block.parent_root));
  var pre_state: BeaconState := tmp_0.copy();
  :- pyassert(get_current_slot(store) >= block.slot);
  var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
  :- pyassert(block.slot > finalized_slot);
  var tmp_1 :- a_(get_ancestor(store, block.parent_root, finalized_slot));
  :- pyassert(tmp_1 == store.finalized_checkpoint.root);
  var state: BeaconState := pre_state.copy();
  :- state_transition(state, signed_block, true);
  store.blocks.set_value(hash_tree_root(block), block);
  store.block_states.set_value(hash_tree_root(block), state);
  var time_into_slot: uint64 := (store.time - store.genesis_time) % SECONDS_PER_SLOT;
  var is_before_attesting_interval: bool := time_into_slot < (SECONDS_PER_SLOT / INTERVALS_PER_SLOT);
  if if (get_current_slot(store) == block.slot) then is_before_attesting_interval else false {
    store.proposer_boost_root := Root_new(hash_tree_root(block));
  }
  if state.current_justified_checkpoint.epoch > store.justified_checkpoint.epoch {
    if state.current_justified_checkpoint.epoch > store.best_justified_checkpoint.epoch {
      store.best_justified_checkpoint := state.current_justified_checkpoint;
    }
    var tmp_2 :- should_update_justified_checkpoint(store, state.current_justified_checkpoint);
    if tmp_2 {
      store.justified_checkpoint := state.current_justified_checkpoint;
    }
  }
  if state.finalized_checkpoint.epoch > store.finalized_checkpoint.epoch {
    store.finalized_checkpoint := state.finalized_checkpoint;
    store.justified_checkpoint := state.current_justified_checkpoint;
  }
}

/*
    Run ``on_attestation`` upon receiving a new ``attestation`` from either within a block or directly on the wire.

    An ``attestation`` that is asserted as invalid may be valid at a later time,
    consider scheduling it for later processing in such case.
    */
method on_attestation(store: Store, attestation: Attestation, is_from_block: bool)
returns (status_: Status) 
{
  :- validate_on_attestation(store, attestation, is_from_block);
  :- store_target_checkpoint_state(store, attestation.data.target);
  var target_state: BeaconState :- a_(store.checkpoint_states.get(attestation.data.target));
  var indexed_attestation: IndexedAttestation := get_indexed_attestation(target_state, attestation);
  :- pyassert(is_valid_indexed_attestation(target_state, indexed_attestation));
  update_latest_messages(store, indexed_attestation.attesting_indices, attestation);
}

/*
    Run ``on_attester_slashing`` immediately upon receiving a new ``AttesterSlashing``
    from either within a block or directly on the wire.
    */
method on_attester_slashing(store: Store, attester_slashing: AttesterSlashing)
returns (status_: Status) 
{
  var attestation_1: IndexedAttestation := attester_slashing.attestation_1;
  var attestation_2: IndexedAttestation := attester_slashing.attestation_2;
  :- pyassert(is_slashable_attestation_data(attestation_1.data, attestation_2.data));
  var state: BeaconState :- a_(store.block_states.get(store.justified_checkpoint.root));
  :- pyassert(is_valid_indexed_attestation(state, attestation_1));
  :- pyassert(is_valid_indexed_attestation(state, attestation_2));
  var indices: Set<ValidatorIndex> := pyset(attestation_1.attesting_indices).intersection(attestation_2.attesting_indices);
  var tmp_for_0: Iterator<ValidatorIndex> := iter(indices);
  while has_next(tmp_for_0) {
    var index: ValidatorIndex := next(tmp_for_0);
    store.equivocating_indices.add(index);
  }
}
