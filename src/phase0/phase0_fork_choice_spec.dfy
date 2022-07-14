include "ssz.dfy"
include "simpletypes.dfy"
include "classes_datatypes.dfy"
include "consts.dfy"

import opened SSZ
import opened SimpleTypes
import opened Classes
import opened Consts

function method get_current_epoch(state: BeaconState): Epoch
function method is_slashable_attestation_data(data1: AttestationData, data2: AttestationData): bool
function method is_valid_indexed_attestation(state: BeaconState, attestation: IndexedAttestation): bool
function method get_indexed_attestation(state: BeaconState, attestation: Attestation): IndexedAttestation
function method get_active_validator_indices(state: BeaconState, epoch: Epoch): seq<ValidatorIndex>
function method get_total_active_balance(state: BeaconState): Gwei
function method process_slots(state_: BeaconState, slot: Slot): Outcome<BeaconState>
function method state_transition(state_: BeaconState, block: SignedBeaconBlock, check: bool): Outcome<BeaconState>

/*
    Return the epoch number at ``slot``.
    */
function method compute_epoch_at_slot(slot: Slot): Epoch
requires SLOTS_PER_EPOCH != 0
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

function method get_forkchoice_store(anchor_state: BeaconState, anchor_block: BeaconBlock): Outcome<Store_dt>
{
  var _ :- pyassert(anchor_block.state_root == hash_tree_root(anchor_state));
  var anchor_root: Root := Root_new(hash_tree_root(anchor_block));
  var anchor_epoch: Epoch := get_current_epoch(anchor_state);
  var justified_checkpoint: Checkpoint := Checkpoint(anchor_epoch, anchor_root);
  var finalized_checkpoint: Checkpoint := Checkpoint(anchor_epoch, anchor_root);
  var proposer_boost_root: Root := Root_new(0);
  Result(Store_dt(uint64_new(anchor_state.genesis_time + (SECONDS_PER_SLOT * anchor_state.slot)), anchor_state.genesis_time, justified_checkpoint, finalized_checkpoint, justified_checkpoint, proposer_boost_root, {}, map[anchor_root := anchor_block.copy()], map[anchor_root := anchor_state.copy()], map[justified_checkpoint := anchor_state.copy()], map[]))
}

function method get_slots_since_genesis(store: Store_dt): int
{
  (store.time - store.genesis_time) / SECONDS_PER_SLOT
}

function method get_current_slot(store: Store_dt): Slot
{
  Slot_new(GENESIS_SLOT + get_slots_since_genesis(store))
}

function method compute_slots_since_epoch_start(slot: Slot): int
{
  slot - compute_start_slot_at_epoch(compute_epoch_at_slot(slot))
}

function method get_ancestor(store: Store_dt, root: Root, slot: Slot): Outcome<Root>
{
  var block: BeaconBlock :- map_get(store.blocks, root);
  if block.slot > slot then
    get_ancestor(store, block.parent_root, slot)
  else
    if block.slot == slot then
      Result(root)
    else
      Result(root)
}

function method get_latest_attesting_balance(store: Store_dt, root: Root): Outcome<Gwei>
{
  var state: BeaconState :- map_get(store.checkpoint_states, store.justified_checkpoint);
  var active_indices: seq<ValidatorIndex> := get_active_validator_indices(state, get_current_epoch(state));
  var tmp_0 :- seq_filter_f((i) =>
      if i in store.latest_messages && i !in store.equivocating_indices then
        var tmp_0 :- map_get(store.latest_messages, i);
        var tmp_1 :- map_get(store.blocks, root);
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
    var tmp_1 :- map_get(store.blocks, root);
    var tmp_2 :- get_ancestor(store, store.proposer_boost_root, tmp_1.slot);
    var proposer_score_2: Gwei :=
      if tmp_2 == root then
        var num_validators: int := |get_active_validator_indices(state, get_current_epoch(state))|;
        var avg_balance: Gwei := get_total_active_balance(state) / num_validators;
        var committee_size: uint64 := num_validators / SLOTS_PER_EPOCH;
        var committee_weight: Gwei := committee_size * avg_balance;
        var proposer_score_1: Gwei := committee_weight * PROPOSER_SCORE_BOOST / 100;
        proposer_score_1
      else
        proposer_score;
  Result(attestation_score + proposer_score_2)
}

function method filter_block_tree(store: Store_dt, block_root: Root, blocks: map<Root,BeaconBlock>): Outcome<(bool, map<Root, BeaconBlock>)>
{
  var block: BeaconBlock :- map_get(store.blocks, block_root);
  var tmp_0 := store.blocks.Keys;
  var tmp_1 :- set_filter_f((root) => var tmp_0 :- map_get(store.blocks, root); Result(tmp_0.parent_root == block_root), tmp_0);
  var children: seq<Root> := set_to_seq(tmp_1);
  if seq_any(children) then
    var loop_body := (x: (seq<bool>, map<Root, BeaconBlock>), child: Root) =>
      var (tmp_1: seq<bool>, blocks: map<Root, BeaconBlock>) := x;
      var (tmp_2, blocks) :- filter_block_tree(store, child, blocks);
      Result(((tmp_1 + [tmp_2]), blocks));
    var (filter_block_tree_result: seq<bool>, blocks) :- seq_loop_f(children, ([], blocks), loop_body);
    if seq_any(filter_block_tree_result) then
      var blocks := blocks[block_root := block];
      Result((true, blocks))
    else
      Result((false, blocks))
  else
    var head_state: BeaconState :- map_get(store.block_states, block_root);
    var correct_justified: bool := store.justified_checkpoint.epoch == GENESIS_EPOCH || head_state.current_justified_checkpoint == store.justified_checkpoint;
    var correct_finalized: bool := store.finalized_checkpoint.epoch == GENESIS_EPOCH || head_state.finalized_checkpoint == store.finalized_checkpoint;
    if correct_justified && correct_finalized then
      var blocks := blocks[block_root := block];
      Result((true, blocks))
    else
      Result((false, blocks))
}

/*
    Retrieve a filtered block tree from ``store``, only returning branches
    whose leaf state's justified/finalized info agrees with that in ``store``.
    */
function method get_filtered_block_tree(store: Store_dt): Outcome<map<Root,BeaconBlock>>
{
  var base: Root := store.justified_checkpoint.root;
  var blocks: map<Root,BeaconBlock> := map[];
  var (_, blocks) :- filter_block_tree(store, base, blocks);
  Result(blocks)
}

function method get_head(store: Store_dt): Outcome<Root>
{
  var blocks: map<Root,BeaconBlock> :- get_filtered_block_tree(store);
  var head: Root := store.justified_checkpoint.root;
  var head_2 := head;
  var loop_body := (head_2: Root, fixpoint: (Root) -> Outcome<Root>) =>
    var tmp_0 := blocks.Keys;
    var tmp_1 :- set_filter_f((root: Root) => var tmp_0 :- map_get(blocks, root); Result(tmp_0.parent_root == head_2), tmp_0);
    var children: seq<Root> := set_to_seq(tmp_1);
    if |children| == 0 then
      Result(head_2)
    else
      var head_1: Root :- seq_max_f(children, (root: Root) => var tmp_0 :- get_latest_attesting_balance(store, root); Result((tmp_0, root)));
      fixpoint(head_1);
  loop_f(head_2, loop_body)
}

/*
    To address the bouncing attack, only update conflicting justified
    checkpoints in the fork choice if in the early slots of the epoch.
    Otherwise, delay incorporation of new justified checkpoint until next epoch boundary.

    See https://ethresear.ch/t/prevention-of-bouncing-attack-on-ffg/6114 for more detailed analysis and discussion.
    */
function method should_update_justified_checkpoint(store: Store_dt, new_justified_checkpoint: Checkpoint): Outcome<bool>
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
}

function method validate_target_epoch_against_current_time(store: Store_dt, attestation: Attestation): Outcome<()>
{
  var target: Checkpoint := attestation.data.target;
  var current_epoch: Epoch := compute_epoch_at_slot(get_current_slot(store));
  var previous_epoch: Epoch := if (current_epoch > GENESIS_EPOCH) then current_epoch - 1 else GENESIS_EPOCH;
  var _ :- pyassert(target.epoch in [current_epoch, previous_epoch]);
  Result(())
}

function method validate_on_attestation(store: Store_dt, attestation: Attestation, is_from_block: bool): Outcome<()>
{
  var target: Checkpoint := attestation.data.target;
  if !is_from_block then
    var _ :- validate_target_epoch_against_current_time(store, attestation);
    Result(())
  else
  var _ :- pyassert(target.epoch == compute_epoch_at_slot(attestation.data.slot));
  var _ :- pyassert(target.root in store.blocks);
  var _ :- pyassert(attestation.data.beacon_block_root in store.blocks);
  var _ :- pyassert(store.blocks[attestation.data.beacon_block_root].slot <= attestation.data.slot);
  var target_slot: Slot := compute_start_slot_at_epoch(target.epoch);
  var tmp_0 :- get_ancestor(store, attestation.data.beacon_block_root, target_slot);
  var _ :- pyassert(target.root == tmp_0);
  var _ :- pyassert(get_current_slot(store) >= (attestation.data.slot + 1));
  Result(())
}

function method store_target_checkpoint_state(store: Store_dt, target: Checkpoint): Outcome<Store_dt>
{
  if target !in store.checkpoint_states then
    var tmp_0 :- map_get(store.block_states, target.root);
    var base_state: BeaconState := tmp_0.copy();
    var base_state :-
      if base_state.slot < compute_start_slot_at_epoch(target.epoch) then
        process_slots(base_state, compute_start_slot_at_epoch(target.epoch))
      else
        Result(base_state);
    var store := store.(checkpoint_states := store.checkpoint_states[target := base_state]);
    Result(store)
  else
    Result(store)
}

function method update_latest_messages(store: Store_dt, attesting_indices: seq<ValidatorIndex>, attestation: Attestation): Store_dt
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

function method on_tick(store: Store_dt, time: uint64): Outcome<Store_dt>
{
  var previous_slot: Slot := get_current_slot(store);
  var store := store.(time := time);
  var current_slot: Slot := get_current_slot(store);
  if current_slot > previous_slot then
    var store := store.(proposer_boost_root := Root_new(0));
    Result(store)
  else
  if !(current_slot > previous_slot && compute_slots_since_epoch_start(current_slot) == 0) then
    Result(store)
  else
  if store.best_justified_checkpoint.epoch > store.justified_checkpoint.epoch then
    var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
    var ancestor_at_finalized_slot: Root :- get_ancestor(store, store.best_justified_checkpoint.root, finalized_slot);
    if ancestor_at_finalized_slot == store.finalized_checkpoint.root then
      var store := store.(justified_checkpoint := store.best_justified_checkpoint);
      Result(store)
    else
      Result(store)
  else
    Result(store)
}

function method on_block(store: Store_dt, signed_block: SignedBeaconBlock): Outcome<Store_dt>
{
  var block: BeaconBlock := signed_block.message;
  var _ :- pyassert(block.parent_root in store.block_states);
  var tmp_0 :- map_get(store.block_states, block.parent_root);
  var pre_state: BeaconState := tmp_0.copy();
  var _ :- pyassert(get_current_slot(store) >= block.slot);
  var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
  var _ :- pyassert(block.slot > finalized_slot);
  var tmp_1 :- get_ancestor(store, block.parent_root, finalized_slot);
  var _ :- pyassert(tmp_1 == store.finalized_checkpoint.root);
  var state: BeaconState := pre_state.copy();
  var state :- state_transition(state, signed_block, true);
  var store := store.(blocks := store.blocks[hash_tree_root(block) := block]);
  var store := store.(block_states := store.block_states[hash_tree_root(block) := state]);
  var time_into_slot: uint64 := (store.time - store.genesis_time) % SECONDS_PER_SLOT;
  var is_before_attesting_interval: bool := time_into_slot < (SECONDS_PER_SLOT / INTERVALS_PER_SLOT);
  var store :=
    if get_current_slot(store) == block.slot && is_before_attesting_interval then
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
      var tmp_2 :- should_update_justified_checkpoint(store, state.current_justified_checkpoint);
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
function method on_attestation(store: Store_dt, attestation: Attestation, is_from_block: bool): Outcome<Store_dt>
{
  var _ :- validate_on_attestation(store, attestation, is_from_block);
  var store :- store_target_checkpoint_state(store, attestation.data.target);
  var target_state: BeaconState :- map_get(store.checkpoint_states, attestation.data.target);
  var indexed_attestation: IndexedAttestation := get_indexed_attestation(target_state, attestation);
  var _ :- pyassert(is_valid_indexed_attestation(target_state, indexed_attestation));
  var store := update_latest_messages(store, indexed_attestation.attesting_indices, attestation);
  Result(store)
}

/*
    Run ``on_attester_slashing`` immediately upon receiving a new ``AttesterSlashing``
    from either within a block or directly on the wire.
    */
function method on_attester_slashing(store: Store_dt, attester_slashing: AttesterSlashing): Outcome<Store_dt>
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
  Result(set_loop(indices, store, loop_body))
}
