include "ssz.dfy"
include "simpletypes.dfy"
include "entities.dfy"
include "consts.dfy"

import opened SSZ
import opened SimpleTypes
import opened Entities
import opened Consts

predicate valid_constants() {
  SECONDS_PER_SLOT != 0
  && SLOTS_PER_EPOCH != 0
  && INTERVALS_PER_SLOT != 0
}

predicate valid_time_slots(store: Store)
  reads store
{
  store.time >= store.genesis_time
}

predicate valid_time_pure(store: Store_dt) {
  store.time >= store.genesis_time
}

predicate valid_blocks(blocks: Dict<Root, BeaconBlock>)
  reads blocks
{
  valid_blocks_pure(blocks.repr)
}

predicate valid_blocks_pure(blocks: map<Root, BeaconBlock>)
{
  forall r :: r in blocks.Keys ==>
    var b := blocks[r];
    b.slot == 0 || (b.parent_root in blocks.Keys && blocks[b.parent_root].slot < b.slot)
}
