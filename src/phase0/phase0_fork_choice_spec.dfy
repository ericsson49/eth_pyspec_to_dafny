include "ssz.dfy"
include "simpletypes.dfy"
include "entities.dfy"
include "consts.dfy"

include "helpers.dfy"

import opened SSZ
import opened SimpleTypes
import opened Entities
import opened Consts

function method get_current_epoch(state: BeaconState): Epoch
function method is_slashable_attestation_data(data1: AttestationData, data2: AttestationData): bool
function method is_valid_indexed_attestation(state: BeaconState, attestation: IndexedAttestation): bool
function method get_indexed_attestation(state: BeaconState, attestation: Attestation): IndexedAttestation
function method get_active_validator_indices(state: BeaconState, epoch: Epoch): seq<ValidatorIndex>
function method get_total_active_balance(state: BeaconState): Gwei
method process_slots(state: BeaconState, slot: Slot) returns (status_: Outcome<BeaconState>)
ensures process_slots_pure(state, slot) == status_
function method process_slots_pure(state: BeaconState, slot: Slot): Outcome<BeaconState>
method state_transition(state: BeaconState, block: SignedBeaconBlock, check: bool)
returns (status_: Outcome<BeaconState>)
ensures state_transition_pure(state, block, check) == status_
function method state_transition_pure(state: BeaconState, block: SignedBeaconBlock, check: bool): Outcome<BeaconState>

/*
    Return the epoch number at ``slot``.
    */
function compute_epoch_at_slot(slot: Slot): Epoch
requires valid_constants()
{
  Epoch_new(slot / SLOTS_PER_EPOCH)
} by method {
  return Epoch_new(slot / SLOTS_PER_EPOCH);
}

/*
    Return the start slot of ``epoch``.
    */
function compute_start_slot_at_epoch(epoch: Epoch): Slot
{
  Slot_new(epoch * SLOTS_PER_EPOCH)
} by method {
  return Slot_new(epoch * SLOTS_PER_EPOCH);
}

method get_forkchoice_store(anchor_state: BeaconState, anchor_block: BeaconBlock)
returns (status_: Outcome<Store>)
{
  var _ :- pyassert(anchor_block.state_root == hash_tree_root(anchor_state));
  var anchor_root: Root := Root_new(hash_tree_root(anchor_block));
  var anchor_epoch: Epoch := get_current_epoch(anchor_state);
  var justified_checkpoint: Checkpoint := Checkpoint(anchor_epoch, anchor_root);
  var finalized_checkpoint: Checkpoint := Checkpoint(anchor_epoch, anchor_root);
  var proposer_boost_root: Root := Root_new(0);
  var tmp_0 := Set_new({});
  var tmp_1: Dict<Root, BeaconBlock> := Dict_new(map[anchor_root := anchor_block.copy()]);
  var tmp_2: Dict<Root, BeaconState> := Dict_new(map[anchor_root := anchor_state.copy()]);
  var tmp_3: Dict<Checkpoint, BeaconState> := Dict_new(map[justified_checkpoint := anchor_state.copy()]);
  var tmp_4 := Dict_new(map[]);
  var tmp_5 := new Store.Init(uint64_new(anchor_state.genesis_time + (SECONDS_PER_SLOT * anchor_state.slot)), anchor_state.genesis_time, justified_checkpoint, finalized_checkpoint, justified_checkpoint, proposer_boost_root, tmp_0, tmp_1, tmp_2, tmp_3, tmp_4);
  return Result(tmp_5);
}

// imperative impure <==> functional impure <==> functional pure
function get_slots_since_genesis(store: Store): (ret: int)
reads store
requires valid_time_slots(store) && valid_constants()
ensures get_slots_since_genesis_pure(store.toPure()) == ret
{
  (store.time - store.genesis_time) / SECONDS_PER_SLOT
} by method {
  return (store.time - store.genesis_time) / SECONDS_PER_SLOT;
}

// functional pure
function get_slots_since_genesis_pure(store: Store_dt): int
requires valid_time_slots_pure(store) && valid_constants()
{
  (store.time - store.genesis_time) / SECONDS_PER_SLOT
}

// imperative impure <==> functional impure <==> functional pure
function get_current_slot(store: Store): (ret: Slot)
reads store
requires valid_time_slots(store) && valid_constants()
ensures get_current_slot_pure(store.toPure()) == ret
{
  Slot_new(GENESIS_SLOT + get_slots_since_genesis(store))
} by method {
  return Slot_new(GENESIS_SLOT + get_slots_since_genesis(store));
}

// functional pure <==> functional impure
function get_current_slot_pure(store: Store_dt): Slot
requires valid_time_slots_pure(store) && valid_constants()
{
  Slot_new(GENESIS_SLOT + get_slots_since_genesis_pure(store))
}

function compute_slots_since_epoch_start(slot: Slot): int
requires valid_constants()
{
  slot - compute_start_slot_at_epoch(compute_epoch_at_slot(slot))
} by method {
  return slot - compute_start_slot_at_epoch(compute_epoch_at_slot(slot));
}

function get_ancestor(store: Store, root: Root, slot: Slot): (ret: Outcome<Root>)
reads store, store.blocks
requires valid_blocks(store.blocks)
ensures get_ancestor_pure(store.toPure(), root, slot) == ret
decreases if !store.blocks.contains(root) then 0 else store.blocks.get_nf(root).slot
{
  assert store.toPure().blocks == store.blocks.repr;
  var block: BeaconBlock :- store.blocks.get(root);
  if block.slot > slot then
    get_ancestor(store, block.parent_root, slot)
  else
    if block.slot == slot then
      Result(root)
    else
      Result(root)
} by method {
  var block: BeaconBlock :- store.blocks.get(root);
  if block.slot > slot {
    return get_ancestor(store, block.parent_root, slot);
  } else {
    if block.slot == slot {
      return Result(root);
    } else {
      return Result(root);
    }
  }
}

function get_ancestor_pure(store: Store_dt, root: Root, slot: Slot): (ret: Outcome<Root>)
requires valid_blocks_pure(store.blocks)
decreases if root !in store.blocks then 0 else store.blocks[root].slot
{
  var block: BeaconBlock :- map_get(store.blocks, root);
  if block.slot > slot then
    get_ancestor_pure(store, block.parent_root, slot)
  else if block.slot == slot then
    Result(root)
  else
    Result(root)
}

function get_latest_attesting_balance(store: Store, root: Root): Outcome<Gwei>
reads store, store.blocks, store.checkpoint_states
requires valid_constants()
requires valid_blocks(store.blocks)
{
  var state: BeaconState :- store.checkpoint_states.get(store.justified_checkpoint);
  var active_indices: seq<ValidatorIndex> := get_active_validator_indices(state, get_current_epoch(state));
  var tmp_0 :- seq_filter_hf((i)
     reads store, store.latest_messages, store.equivocating_indices, store.blocks
     requires valid_blocks(store.blocks)
   =>
      if store.latest_messages.contains(i) && !store.equivocating_indices.contains(i) then
        var tmp_0 :- store.latest_messages.get(i);
        var tmp_1 :- store.blocks.get(root);
        var tmp_2 :- get_ancestor(store, tmp_0.root, tmp_1.slot);
        Result(tmp_2 == root)
      else Result(false),
    active_indices);
  var tmp_1 :- seq_map_f((i) => var tmp_0 :- seq_get(state.validators, i); Result(tmp_0.effective_balance), tmp_0);
  var attestation_score: Gwei := Gwei_new(seq_sum(tmp_1));
  if store.proposer_boost_root == Root_new(0) then
    Result(attestation_score)
  else
    var proposer_score: Gwei := Gwei_new(0);
    var tmp_2 :- store.blocks.get(root);
    var tmp_3 :- get_ancestor(store, store.proposer_boost_root, tmp_2.slot);
    var proposer_score_2: Gwei :-
      if tmp_3 == root then
        var num_validators: int := |get_active_validator_indices(state, get_current_epoch(state))|;
        var _ :- if num_validators == 0 then Exception else Result(());
        var avg_balance: Gwei := get_total_active_balance(state) / num_validators;
        var committee_size: uint64 := num_validators / SLOTS_PER_EPOCH;
        var committee_weight: Gwei := committee_size * avg_balance;
        var proposer_score_1: Gwei := committee_weight * PROPOSER_SCORE_BOOST / 100;
        Result(proposer_score_1)
      else
        Result(proposer_score);
    Result(attestation_score + proposer_score_2)
} by method {
  var state: BeaconState :- store.checkpoint_states.get(store.justified_checkpoint);
  var active_indices: seq<ValidatorIndex> := get_active_validator_indices(state, get_current_epoch(state));
  var tmp_0 :- seq_filter_hf((i)
     reads store, store.latest_messages, store.equivocating_indices, store.blocks
     requires valid_blocks(store.blocks)
   =>
      if store.latest_messages.contains(i) && !store.equivocating_indices.contains(i) then
        var tmp_0 :- store.latest_messages.get(i);
        var tmp_1 :- store.blocks.get(root);
        var tmp_2 :- get_ancestor(store, tmp_0.root, tmp_1.slot);
        Result(tmp_2 == root)
      else Result(false),
    active_indices);
  var tmp_1 :- seq_map_f((i) => var tmp_0 :- seq_get(state.validators, i); Result(tmp_0.effective_balance), tmp_0);
  var attestation_score: Gwei := Gwei_new(seq_sum(tmp_1));
  if store.proposer_boost_root == Root_new(0) {
    return Result(attestation_score);
  }
  var proposer_score: Gwei := Gwei_new(0);
  var tmp_2 :- store.blocks.get(root);
  var tmp_3 :- get_ancestor(store, store.proposer_boost_root, tmp_2.slot);
  var proposer_score_2: Gwei :-
    if tmp_3 == root then
      var num_validators: int := |get_active_validator_indices(state, get_current_epoch(state))|;
      var _ :- if num_validators == 0 then Exception else Result(());
      var avg_balance: Gwei := get_total_active_balance(state) / num_validators;
      var committee_size: uint64 := num_validators / SLOTS_PER_EPOCH;
      var committee_weight: Gwei := committee_size * avg_balance;
      var proposer_score_1: Gwei := committee_weight * PROPOSER_SCORE_BOOST / 100;
      Result(proposer_score_1)
    else
      Result(proposer_score);
  return Result(attestation_score + proposer_score_2);
}

method filter_block_tree(store: Store, block_root: Root, blocks: Dict<Root,BeaconBlock>)
returns (status_: Outcome<bool>) 
modifies blocks
{
  var block: BeaconBlock :- store.blocks.get(block_root);
  var tmp_0 := store.blocks.keys();
  var tmp_1 :- set_filter_hf((root) reads store, store.blocks => var tmp_0 :- store.blocks.get(root); Result(tmp_0.parent_root == block_root), tmp_0);
  var children: seq<Root> := set_to_seq(tmp_1);
  if seq_any(children) {
    var tmp_0 := children;
    var tmp_1 := PyList_new([]);
    while tmp_0 != [] decreases tmp_0 {
      var child := tmp_0[0];
      tmp_0 := tmp_0[1..];
      var tmp_2 :- filter_block_tree(store, child, blocks);
      tmp_1.append(tmp_2);
    }
    var filter_block_tree_result: PyList<bool> := pylist(tmp_1);
    if any(filter_block_tree_result) {
      blocks.set_value(block_root, block);
      return Result(true);
    }
    return Result(false);
  }
  var head_state: BeaconState :- store.block_states.get(block_root);
  var correct_justified: bool := store.justified_checkpoint.epoch == GENESIS_EPOCH || head_state.current_justified_checkpoint == store.justified_checkpoint;
  var correct_finalized: bool := store.finalized_checkpoint.epoch == GENESIS_EPOCH || head_state.finalized_checkpoint == store.finalized_checkpoint;
  if correct_justified && correct_finalized {
    blocks.set_value(block_root, block);
    return Result(true);
  }
  return Result(false);
}

/*
    Retrieve a filtered block tree from ``store``, only returning branches
    whose leaf state's justified/finalized info agrees with that in ``store``.
    */
method get_filtered_block_tree(store: Store)
returns (status_: Outcome<Dict<Root,BeaconBlock>>) 
{
  var base: Root := store.justified_checkpoint.root;
  var blocks: Dict<Root,BeaconBlock> := Dict_new(map[]);
  var _ := filter_block_tree(store, base, blocks);
  return Result(blocks);
}

method get_head(store: Store)
returns (status_: Outcome<Root>) 
requires valid_constants()
requires valid_blocks(store.blocks)
decreases *
{
  var blocks: Dict<Root,BeaconBlock> :- get_filtered_block_tree(store);
  var head: Root := store.justified_checkpoint.root;
  var head_2 := head;
  while true decreases * {
    var tmp_0 := Set_new(blocks.keys());
    var tmp_1 :- filter_f((root) reads blocks => var tmp_0 :- blocks.get(root); Result(tmp_0.parent_root == head_2), tmp_0);
    var children: PyList<Root> := pylist(tmp_1);
    if len(children) == 0 {
      return Result(head_2);
    }
    var head_1: Root :- max_hf(children,
      (root: Root)
        reads store, store.blocks, store.checkpoint_states
        requires valid_blocks(store.blocks)
      => var tmp_0 :- get_latest_attesting_balance(store, root); Result((tmp_0, root)));
    head_2 := head_1;
  }
}

/*
    To address the bouncing attack, only update conflicting justified
    checkpoints in the fork choice if in the early slots of the epoch.
    Otherwise, delay incorporation of new justified checkpoint until next epoch boundary.

    See https://ethresear.ch/t/prevention-of-bouncing-attack-on-ffg/6114 for more detailed analysis and discussion.
    */
function should_update_justified_checkpoint(store: Store, new_justified_checkpoint: Checkpoint): (ret: Outcome<bool>)
reads store, store.blocks
requires valid_time_slots(store) && valid_constants()
requires valid_blocks(store.blocks)
ensures should_update_justified_checkpoint_pure(store.toPure(), new_justified_checkpoint)
        == ret
{
  if compute_slots_since_epoch_start(get_current_slot(store)) < SAFE_SLOTS_TO_UPDATE_JUSTIFIED then
    Result(true)
  else
    var justified_slot: Slot := compute_start_slot_at_epoch(store.justified_checkpoint.epoch);
    var tmp_0 :- get_ancestor(store, new_justified_checkpoint.root, justified_slot);
    if !(tmp_0 == store.justified_checkpoint.root) then
      Result(false)
    else
      Result(true)
} by method {
  if compute_slots_since_epoch_start(get_current_slot(store)) < SAFE_SLOTS_TO_UPDATE_JUSTIFIED {
    return Result(true);
  }
  var justified_slot: Slot := compute_start_slot_at_epoch(store.justified_checkpoint.epoch);
  var tmp_0 :- get_ancestor(store, new_justified_checkpoint.root, justified_slot);
  if !(tmp_0 == store.justified_checkpoint.root) {
    return Result(false);
  } else {
    return Result(true);
  }
}

function should_update_justified_checkpoint_pure(store: Store_dt, new_justified_checkpoint: Checkpoint): Outcome<bool>
requires valid_time_slots_pure(store) && valid_constants()
requires valid_blocks_pure(store.blocks)
{
  if compute_slots_since_epoch_start(get_current_slot_pure(store)) < SAFE_SLOTS_TO_UPDATE_JUSTIFIED then
    Result(true)
  else
    var justified_slot: Slot := compute_start_slot_at_epoch(store.justified_checkpoint.epoch);
    var tmp_0 :- get_ancestor_pure(store, new_justified_checkpoint.root, justified_slot);
    if !(tmp_0 == store.justified_checkpoint.root) then
      Result(false)
    else
      Result(true)
}


function validate_target_epoch_against_current_time(store: Store, attestation: Attestation): (ret: Outcome<()>)
reads store
requires valid_constants()
requires valid_time_slots(store)
ensures validate_target_epoch_against_current_time_pure(store.toPure(), attestation)
        == ret
{
  var target: Checkpoint := attestation.data.target;
  var current_epoch: Epoch := compute_epoch_at_slot(get_current_slot(store));
  var previous_epoch: Epoch := if (current_epoch > GENESIS_EPOCH) then current_epoch - 1 else GENESIS_EPOCH;
  var _ :- pyassert(target.epoch in [current_epoch, previous_epoch]);
  Result(())
} by method {
  var target: Checkpoint := attestation.data.target;
  var current_epoch: Epoch := compute_epoch_at_slot(get_current_slot(store));
  var previous_epoch: Epoch := if (current_epoch > GENESIS_EPOCH) then current_epoch - 1 else GENESIS_EPOCH;
  var tmp_0 := PyList_new([current_epoch, previous_epoch]);
  var _ :- pyassert(tmp_0.contains(target.epoch));
  return Result(());
}

function validate_target_epoch_against_current_time_pure(store: Store_dt, attestation: Attestation): Outcome<()>
requires valid_constants()
requires valid_time_slots_pure(store)
{
  var target: Checkpoint := attestation.data.target;
  var current_epoch: Epoch := compute_epoch_at_slot(get_current_slot_pure(store));
  var previous_epoch: Epoch := if (current_epoch > GENESIS_EPOCH) then current_epoch - 1 else GENESIS_EPOCH;
  var _ :- pyassert(target.epoch in [current_epoch, previous_epoch]);
  Result(())
}

function validate_on_attestation(store: Store, attestation: Attestation, is_from_block: bool): (ret: Outcome<()>)
reads store, store.blocks
requires valid_constants()
requires valid_time_slots(store)
requires valid_blocks(store.blocks)
ensures validate_on_attestation_pure(store.toPure(), attestation, is_from_block)
        == ret
{
  var target: Checkpoint := attestation.data.target;
  var _ :- if !is_from_block then
    validate_target_epoch_against_current_time(store, attestation)
  else
    Result(());
  var _ :- pyassert(target.epoch == compute_epoch_at_slot(attestation.data.slot));
  var _ :- pyassert(store.blocks.contains(target.root));
  var _ :- pyassert(store.blocks.contains(attestation.data.beacon_block_root));
  var _ :- pyassert(store.blocks.get_nf(attestation.data.beacon_block_root).slot <= attestation.data.slot);
  var target_slot: Slot := compute_start_slot_at_epoch(target.epoch);
  var tmp_0 :- get_ancestor(store, attestation.data.beacon_block_root, target_slot);
  var _ :- pyassert(target.root == tmp_0);
  var _ :- pyassert(get_current_slot(store) >= (attestation.data.slot + 1));
  Result(())
} by method {
  var target: Checkpoint := attestation.data.target;
  if !is_from_block {
    var _ :- validate_target_epoch_against_current_time(store, attestation);
  }
  var _ :- pyassert(target.epoch == compute_epoch_at_slot(attestation.data.slot));
  var _ :- pyassert(store.blocks.contains(target.root));
  var _ :- pyassert(store.blocks.contains(attestation.data.beacon_block_root));
  var _ :- pyassert(store.blocks.get_nf(attestation.data.beacon_block_root).slot <= attestation.data.slot);
  var target_slot: Slot := compute_start_slot_at_epoch(target.epoch);
  var tmp_0 :- get_ancestor(store, attestation.data.beacon_block_root, target_slot);
  var _ :- pyassert(target.root == tmp_0);
  var _ :- pyassert(get_current_slot(store) >= (attestation.data.slot + 1));
  return Result(());
}

function validate_on_attestation_pure(store: Store_dt, attestation: Attestation, is_from_block: bool): Outcome<()>
requires valid_constants()
requires valid_time_slots_pure(store)
requires valid_blocks_pure(store.blocks)
{
  var target: Checkpoint := attestation.data.target;
  var _ :- if !is_from_block then
    validate_target_epoch_against_current_time_pure(store, attestation)
  else
    Result(());
  var _ :- pyassert(target.epoch == compute_epoch_at_slot(attestation.data.slot));
  var _ :- pyassert(target.root in store.blocks);
  var _ :- pyassert(attestation.data.beacon_block_root in store.blocks);
  var _ :- pyassert(store.blocks[attestation.data.beacon_block_root].slot <= attestation.data.slot);
  var target_slot: Slot := compute_start_slot_at_epoch(target.epoch);
  var tmp_0 :- get_ancestor_pure(store, attestation.data.beacon_block_root, target_slot);
  var _ :- pyassert(target.root == tmp_0);
  var _ :- pyassert(get_current_slot_pure(store) >= (attestation.data.slot + 1));
  Result(())
}

method store_target_checkpoint_state(store: Store, target: Checkpoint)
returns (status_: Outcome<()>) 
modifies store.checkpoint_states
ensures var pure_ret := store_target_checkpoint_state_pure(old(store.toPure()), target);
        && !status_.IsFailure() <==> !pure_ret.IsFailure()
        && !status_.IsFailure() ==> store.toPure() == pure_ret.Extract()
{
  assert store.toPure().blocks == store.blocks.repr;
  status_ := Result(());
  if !store.checkpoint_states.contains(target) {
    var tmp_0 :- store.block_states.get(target.root);
    var base_state: BeaconState := tmp_0.copy();
    if base_state.slot < compute_start_slot_at_epoch(target.epoch) {
      base_state :- process_slots(base_state, compute_start_slot_at_epoch(target.epoch));
    }
    store.checkpoint_states.set_value(target, base_state);
  }
}

function store_target_checkpoint_state_pure(store: Store_dt, target: Checkpoint): Outcome<Store_dt>
{
  if target !in store.checkpoint_states then
    var tmp_0 :- map_get(store.block_states, target.root);
    var base_state: BeaconState := tmp_0.copy();
    var base_state :-
      if base_state.slot < compute_start_slot_at_epoch(target.epoch) then
        process_slots_pure(base_state, compute_start_slot_at_epoch(target.epoch))
      else
        Result(base_state);
    var store := store.(checkpoint_states := store.checkpoint_states[target := base_state]);
    Result(store)
  else
    Result(store)
} by method {
  var store := store;
  if target !in store.checkpoint_states {
    var tmp_0 :- map_get(store.block_states, target.root);
    var base_state: BeaconState := tmp_0.copy();
    if base_state.slot < compute_start_slot_at_epoch(target.epoch) {
      base_state :- process_slots(base_state, compute_start_slot_at_epoch(target.epoch));
    }
    store := store.(checkpoint_states := store.checkpoint_states[target := base_state]);
  }
  return Result(store);
}


method update_latest_messages(store: Store, attesting_indices: seq<ValidatorIndex>, attestation: Attestation)
modifies store.latest_messages
ensures store.toPure() == update_latest_messages_pure(old(store.toPure()), attesting_indices, attestation)
{
  var target: Checkpoint := attestation.data.target;
  var beacon_block_root: Root := attestation.data.beacon_block_root;
  var non_equivocating_attesting_indices: seq<ValidatorIndex> := seq_filter_h((i) reads store, store.equivocating_indices => !store.equivocating_indices.contains(i), attesting_indices);
  var tmp := store.equivocating_indices.repr;
  assume non_equivocating_attesting_indices == seq_filter((i) => i !in tmp, attesting_indices);
  var tmp_for_0: seq<ValidatorIndex> := non_equivocating_attesting_indices;
  
  ghost var processed: seq<ValidatorIndex> := [];
  ghost var loop_body := (store: Store_dt, i: ValidatorIndex) =>
    if i !in store.latest_messages || target.epoch > store.latest_messages[i].epoch then
      store.(latest_messages := store.latest_messages[i := LatestMessage(target.epoch, beacon_block_root)])
    else
      store;
  while tmp_for_0 != [] decreases tmp_for_0
  invariant processed + tmp_for_0 == non_equivocating_attesting_indices
  invariant seq_loop(processed, old(store.toPure()), loop_body) == store.toPure()
  {
    var i: ValidatorIndex := tmp_for_0[0];
    tmp_for_0 := tmp_for_0[1..];
    if !store.latest_messages.contains(i) || target.epoch > store.latest_messages.get_nf(i).epoch {
      store.latest_messages.set_value(i, LatestMessage(target.epoch, beacon_block_root));
    }
    processed := processed + [i];
  }
  assert processed == non_equivocating_attesting_indices;
}

function update_latest_messages_pure(store: Store_dt, attesting_indices: seq<ValidatorIndex>, attestation: Attestation): Store_dt
{
  var target: Checkpoint := attestation.data.target;
  var beacon_block_root: Root := attestation.data.beacon_block_root;
  var non_equivocating_attesting_indices: seq<ValidatorIndex> := seq_filter((i) => i !in store.equivocating_indices, attesting_indices);
  var loop_body := (store: Store_dt, i: ValidatorIndex) =>
    if i !in store.latest_messages || target.epoch > store.latest_messages[i].epoch then
      store.(latest_messages := store.latest_messages[i := LatestMessage(target.epoch, beacon_block_root)])
    else
      store;
  var store := seq_loop(non_equivocating_attesting_indices, store, loop_body);
  store
}

method on_tick(store: Store, time: uint64)
returns (status_: Outcome<()>) 
requires time >= store.time
requires valid_constants()
requires valid_time_slots(store)
requires valid_blocks(store.blocks)
modifies store
ensures !status_.IsFailure() <==> !on_tick_pure(old(store.toPure()), time).IsFailure()
ensures !status_.IsFailure() ==> store.toPure() == on_tick_pure(old(store.toPure()), time).Extract()
{
  status_ := Result(());
  var previous_slot: Slot := get_current_slot(store);
  store.time := time;
  var current_slot: Slot := get_current_slot(store);
  if current_slot > previous_slot {
    store.proposer_boost_root := Root_new(0);
  }
  if !(current_slot > previous_slot && compute_slots_since_epoch_start(current_slot) == 0) {
    return;
  }
  if store.best_justified_checkpoint.epoch > store.justified_checkpoint.epoch {
    var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
    var ancestor_at_finalized_slot :- get_ancestor(store, store.best_justified_checkpoint.root, finalized_slot);
    if ancestor_at_finalized_slot == store.finalized_checkpoint.root {
      store.justified_checkpoint := store.best_justified_checkpoint;
    }
  }
}

function on_tick_pure(store: Store_dt, time: uint64): Outcome<Store_dt>
requires time >= store.time
requires valid_constants()
requires valid_time_slots_pure(store)
requires valid_blocks_pure(store.blocks)
{
  var previous_slot: Slot := get_current_slot_pure(store);
  var store := store.(time := time);
  var current_slot: Slot := get_current_slot_pure(store);
  var store := if current_slot > previous_slot then
    var store := store.(proposer_boost_root := Root_new(0));
    store
  else
    store;
  if !(current_slot > previous_slot && compute_slots_since_epoch_start(current_slot) == 0) then
    Result(store)
  else
    if store.best_justified_checkpoint.epoch > store.justified_checkpoint.epoch then
      var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
      var ancestor_at_finalized_slot: Root :- get_ancestor_pure(store, store.best_justified_checkpoint.root, finalized_slot);
      if ancestor_at_finalized_slot == store.finalized_checkpoint.root then
        var store := store.(justified_checkpoint := store.best_justified_checkpoint);
        Result(store)
      else
        Result(store)
    else
      Result(store)
} 

method on_block(store: Store, signed_block: SignedBeaconBlock)
returns (status_: Outcome<()>) 
requires valid_constants()
requires valid_time_slots(store)
requires valid_blocks(store.blocks)
modifies store, store.blocks, store.block_states
ensures var pure_out := on_block_pure(old(store.toPure()), signed_block);
        && !status_.IsFailure() <==> !pure_out.IsFailure()
        && !status_.IsFailure() ==> store.toPure() == pure_out.Extract()
{
  status_ := Result(());
  var block: BeaconBlock := signed_block.message;
  var _ :- pyassert(store.block_states.contains(block.parent_root));
  var tmp_0 :- store.block_states.get(block.parent_root);
  var pre_state: BeaconState := tmp_0.copy();
  var _ :- pyassert(get_current_slot(store) >= block.slot);
  var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
  var _ :- pyassert(block.slot > finalized_slot);
  var tmp_1 :- get_ancestor(store, block.parent_root, finalized_slot);
  var _ :- pyassert(tmp_1 == store.finalized_checkpoint.root);
  var state: BeaconState := pre_state.copy();
  state :- state_transition(state, signed_block, true);
  store.blocks.set_value(hash_tree_root(block), block);
  assume valid_blocks(store.blocks);
  store.block_states.set_value(hash_tree_root(block), state);
  var time_into_slot: uint64 := (store.time - store.genesis_time) % SECONDS_PER_SLOT;
  var is_before_attesting_interval: bool := time_into_slot < (SECONDS_PER_SLOT / INTERVALS_PER_SLOT);
  if get_current_slot(store) == block.slot && is_before_attesting_interval {
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

function on_block_pure(store: Store_dt, signed_block: SignedBeaconBlock): Outcome<Store_dt>
requires valid_constants()
requires valid_time_slots_pure(store)
requires valid_blocks_pure(store.blocks)
{
  var block: BeaconBlock := signed_block.message;
  var _ :- pyassert(block.parent_root in store.block_states);
  var tmp_0 :- map_get(store.block_states, block.parent_root);
  var pre_state: BeaconState := tmp_0.copy();
  var _ :- pyassert(get_current_slot_pure(store) >= block.slot);
  var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
  var _ :- pyassert(block.slot > finalized_slot);
  var tmp_1 :- get_ancestor_pure(store, block.parent_root, finalized_slot);
  var _ :- pyassert(tmp_1 == store.finalized_checkpoint.root);
  var state: BeaconState := pre_state.copy();
  var state :- state_transition_pure(state, signed_block, true);
  var store := store.(blocks := store.blocks[hash_tree_root(block) := block]);
  assume valid_blocks_pure(store.blocks);
  var store := store.(block_states := store.block_states[hash_tree_root(block) := state]);
  var time_into_slot: uint64 := (store.time - store.genesis_time) % SECONDS_PER_SLOT;
  var is_before_attesting_interval: bool := time_into_slot < (SECONDS_PER_SLOT / INTERVALS_PER_SLOT);
  var store :=
    if get_current_slot_pure(store) == block.slot && is_before_attesting_interval then
      store.(proposer_boost_root := Root_new(hash_tree_root(block)))
    else
      store;
  var store :-
    if state.current_justified_checkpoint.epoch > store.justified_checkpoint.epoch then
      var store :=
        if state.current_justified_checkpoint.epoch > store.best_justified_checkpoint.epoch then
          store.(best_justified_checkpoint := state.current_justified_checkpoint)
        else
          store;
      var tmp_2 :- should_update_justified_checkpoint_pure(store, state.current_justified_checkpoint);
      var store :=
        if tmp_2 then
          store.(justified_checkpoint := state.current_justified_checkpoint)
        else
          store;
      Result(store)
    else
      Result(store);
  var store :=
    if state.finalized_checkpoint.epoch > store.finalized_checkpoint.epoch then
      var store := store.(finalized_checkpoint := state.finalized_checkpoint);
      store.(justified_checkpoint := state.current_justified_checkpoint)
    else
      store;
  Result(store)
} 

/*
    Run ``on_attestation`` upon receiving a new ``attestation`` from either within a block or directly on the wire.

    An ``attestation`` that is asserted as invalid may be valid at a later time,
    consider scheduling it for later processing in such case.
    */
method on_attestation(store: Store, attestation: Attestation, is_from_block: bool)
returns (status_: Outcome<()>) 
requires valid_constants()
requires valid_time_slots(store)
requires valid_blocks(store.blocks)
modifies store.latest_messages, store.checkpoint_states
ensures var pure_out := on_attestation_pure(old(store.toPure()), attestation, is_from_block);
        && !status_.IsFailure() <==> !pure_out.IsFailure()
        && !status_.IsFailure() ==> store.toPure() == pure_out.Extract()
{
  status_ := Result(());
  var _ :- validate_on_attestation(store, attestation, is_from_block);
  var _ :- store_target_checkpoint_state(store, attestation.data.target);
  var target_state: BeaconState :- store.checkpoint_states.get(attestation.data.target);
  var indexed_attestation: IndexedAttestation := get_indexed_attestation(target_state, attestation);
  var _ :- pyassert(is_valid_indexed_attestation(target_state, indexed_attestation));
  update_latest_messages(store, indexed_attestation.attesting_indices, attestation);
}

function on_attestation_pure(store: Store_dt, attestation: Attestation, is_from_block: bool): Outcome<Store_dt>
requires valid_constants()
requires valid_time_slots_pure(store)
requires valid_blocks_pure(store.blocks)
{
  var _ :- validate_on_attestation_pure(store, attestation, is_from_block);
  var store :- store_target_checkpoint_state_pure(store, attestation.data.target);
  var tmp := map_get(store.checkpoint_states, attestation.data.target);
  if tmp.IsFailure() then
    Exception
  else
  var target_state: BeaconState := tmp.Extract();
  var indexed_attestation: IndexedAttestation := get_indexed_attestation(target_state, attestation);
  var _ :- pyassert(is_valid_indexed_attestation(target_state, indexed_attestation));
  var store := update_latest_messages_pure(store, indexed_attestation.attesting_indices, attestation);
  Result(store)
} 

/*
    Run ``on_attester_slashing`` immediately upon receiving a new ``AttesterSlashing``
    from either within a block or directly on the wire.
    */
method on_attester_slashing(store: Store, attester_slashing: AttesterSlashing)
returns (status_: Outcome<()>) 
modifies store.equivocating_indices
{
  status_ := Result(());
  var attestation_1: IndexedAttestation := attester_slashing.attestation_1;
  var attestation_2: IndexedAttestation := attester_slashing.attestation_2;
  var _ :- pyassert(is_slashable_attestation_data(attestation_1.data, attestation_2.data));
  var state: BeaconState :- store.block_states.get(store.justified_checkpoint.root);
  var _ :- pyassert(is_valid_indexed_attestation(state, attestation_1));
  var _ :- pyassert(is_valid_indexed_attestation(state, attestation_2));
  var indices: set<ValidatorIndex> := seq_to_set(attestation_1.attesting_indices) * seq_to_set(attestation_2.attesting_indices);
  var tmp_for_0: set<ValidatorIndex> := indices;
  while tmp_for_0 != {} decreases tmp_for_0 {
    var index: ValidatorIndex :| index in tmp_for_0;
    tmp_for_0 := tmp_for_0 - {index};
    store.equivocating_indices.add(index);
  }
}

function method seq_intersection<T>(a: seq<T>, b: seq<T>): seq<T>

function on_attester_slashing_pure(store: Store_dt, attester_slashing: AttesterSlashing): Outcome<Store_dt>
{
  var attestation_1: IndexedAttestation := attester_slashing.attestation_1;
  var attestation_2: IndexedAttestation := attester_slashing.attestation_2;
  var _ :- pyassert(is_slashable_attestation_data(attestation_1.data, attestation_2.data));
  var state: BeaconState :- map_get(store.block_states, store.justified_checkpoint.root);
  var _ :- pyassert(is_valid_indexed_attestation(state, attestation_1));
  var _ :- pyassert(is_valid_indexed_attestation(state, attestation_2));
  var indices: set<ValidatorIndex> := seq_to_set(attestation_1.attesting_indices) * seq_to_set(attestation_2.attesting_indices);
  var loop_body := (store: Store_dt, index: ValidatorIndex) =>
    store.(equivocating_indices := store.equivocating_indices + {index});
  var store := set_loop(indices, store, loop_body);
  Result(store)
} by method {
  var store := store;
  var attestation_1: IndexedAttestation := attester_slashing.attestation_1;
  var attestation_2: IndexedAttestation := attester_slashing.attestation_2;
  var _ :- pyassert(is_slashable_attestation_data(attestation_1.data, attestation_2.data));
  var state: BeaconState :- map_get(store.block_states, store.justified_checkpoint.root);
  var _ :- pyassert(is_valid_indexed_attestation(state, attestation_1));
  var _ :- pyassert(is_valid_indexed_attestation(state, attestation_2));
  var indices: set<ValidatorIndex> := seq_to_set(attestation_1.attesting_indices) * seq_to_set(attestation_2.attesting_indices);
  var tmp_for_0: set<ValidatorIndex> := indices;
  while tmp_for_0 != {} decreases tmp_for_0 {
    var index: ValidatorIndex :| index in tmp_for_0;
    tmp_for_0 := tmp_for_0 - {index};
    store := store.(equivocating_indices := store.equivocating_indices + {index});
  }
  return Result(store);
}