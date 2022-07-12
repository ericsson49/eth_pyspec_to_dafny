module SSZ {
    datatype Status =
    | Success
    | Failure
    {
        predicate method IsFailure() { this.Failure?  }
        function method PropagateFailure(): Status
            requires IsFailure()
        {
            Failure
        }
    }

    /*method a_<T>(r: (Status, T)) returns (status_: Status, ret_: T) {
        ret_ :- r.0, r.1;
    }*/

    function method b_<T>(r: Outcome<T>): NEOutcome
    {
        if r.IsFailure() then
            NEException
        else
            NEResult(r.Extract())
    }

    datatype Outcome<T> =
    | Result(value: T)
    | Exception
    {
        predicate method IsFailure() { this.Exception?  }
        function method Extract(): T
            requires !IsFailure()
        {
            this.value
        }
        function method PropagateFailure<U>(): Outcome<U>
            requires IsFailure()
        {
            Exception
        }
    }

    datatype NEOutcome<T> =
    | NEResult(value: T)
    | NEException
    {
        predicate method IsFailure() { this.NEException?  }
        function method PropagateFailure<U>(): NEOutcome<U>
            requires IsFailure()
        {
            NEException
        }
    }

    type uint64 = nat
    type boolean = nat
    type Bytes1 = nat
    type Bytes4 = nat
    type Bytes32 = nat
    type Bytes48 = nat
    type Bytes96 = nat
    trait Iterator<T> {
        ghost var decreases_ : nat;
        function method has_next(): bool
        ensures decreases_ > 0 <==> has_next()
        method next() returns (ret_: T)
        requires has_next()
        modifies this
        ensures old(decreases_) == decreases_ + 1
    }
    trait Collection<T> {
        function method contains(k: T): bool reads this
    }
    trait Sequence<T> extends Collection<T> {
        function method get(k: nat): Outcome<T>
        function method get_nf(i: nat): T
    }
    class Dict<K(==),V> {
        var repr: map<K,V>;
        constructor empty()
        function values(): set<V> reads this {
            repr.Values
        }
        function method keys(): set<K> reads this {
            repr.Keys
        }
        function method contains(k: K): bool
        reads this
        ensures contains(k) <==> k in repr
        {
            k in repr
        }
        function method get_s(k: K): (Status, V) reads this
        ensures !get_s(k).0.IsFailure() <==> k in repr
        ensures !get_s(k).0.IsFailure() ==> get_s(k).1 == repr[k]
        function method get_nf(k: K): V reads this requires contains(k) {
            repr[k]
        }
        function method get(k: K): Outcome<V> reads this
        ensures !get(k).IsFailure() <==> k in repr
        ensures !get(k).IsFailure() ==> get(k).Extract() == repr[k]
        method set_value(k: K, v: V) modifies this
        ensures old(repr)[k := v] == repr
        {
            repr := repr[k := v];
        }
    }
    class Set<T(==)> extends Collection<T> {
        var repr: set<T>
        constructor empty() {}
        constructor(t: set<T>) {}
        function method contains(k: T): bool reads this
        function method intersection(s: Sequence<T>): Set<T>
        method add(e: T) modifies this
    }
    class PyList<T(==)> extends Sequence<T> {
        var repr: seq<T>
        constructor empty() {}
        constructor(t: seq<T>) {}
        function method contains(k: T): bool reads this
        function method get(k: nat): Outcome<T>
        function method get_nf(i: nat): T
        method append(e: T) modifies this
    }
    class ssz_List<T> extends Sequence<T> {
        function method contains(k: T): bool reads this
        function method get(k: nat): Outcome<T>
        function method get_nf(i: nat): T
    }
    class ssz_Vector<T> extends Sequence<T> {
        function method contains(k: T): bool reads this
        function method get(k: nat): Outcome<T>
        function method get_nf(i: nat): T
    }
    type Bitlist = ssz_List<boolean>
    type Bitvector = ssz_Vector<boolean>

    function method hash(a: nat): Bytes32
    function method hash_tree_root<T>(a: T): Bytes32

    method iter<T>(a: Collection<T>) returns (ret_: Iterator<T>) ensures fresh(ret_)
    function method has_next<T>(a: Iterator<T>): bool {
        a.has_next()
    }
    method next<T>(a: Iterator<T>)
    returns (ret_: T)
    requires a.has_next()
    modifies a
    ensures old(a.decreases_) == a.decreases_ + 1
    {
        ret_ := a.next();
    }

    function method len<T>(a: Collection<T>): nat
    function method seq_get<T>(a: Sequence<T>, i: nat): T

    function method pyassert_(b: bool): NEOutcome<()>
    ensures b <==> !pyassert(b).IsFailure()
    {
      if b then NEResult(()) else NEException
    }

    function method pyassert(b: bool): Outcome<()>
    ensures b <==> !pyassert(b).IsFailure()
    {
      if b then Result(()) else Exception
    }

    function method Bitlist_new(a: seq<bool>): Bitlist
    function method Bitvector_new(): Bitvector
    method Dict_new<K,V>(a: map<K,V>) returns (ret_: Dict<K,V>) ensures ret_.repr == a && fresh(ret_)

    method PyList_empty<T>() returns (ret_: PyList<T>)
    ensures ret_.repr == [] && fresh(ret_)
    {
        ret_ := PyList_new([]);
    }
    method PyList_new<T>(a: seq<T>) returns (ret_: PyList<T>) ensures ret_.repr == a && fresh(ret_)
    method Set_empty<T>() returns (ret_: Set<T>) { ret_ := Set_new({}); }
    method Set_new<T>(a: set<T>) returns (ret_: Set<T>) ensures ret_.repr == a && fresh(ret_)
    function method List_new<T>(a: seq<T>): ssz_List<T>
    function method Vector_new<T>(): ssz_Vector<T>

    function method pylist<T>(s: Collection<T>): PyList<T>
    function method pyset<T>(s: Collection<T>): Set<T>
    function method any<T>(s: Sequence<T>): bool
    function method all<T>(s: Sequence<T>): bool

    function method filter<T>(f: (T) -> bool, s: Collection<T>): Sequence<T>
    function method filter_f<T>(f: (T) -> Outcome<bool>, s: Collection<T>): Outcome<Sequence<T>>
    function method pymap<A,B>(f: (A) -> B, s: Collection<A>): Sequence<B>
    function method pymap_f<A,B>(f: (A) -> Outcome<B>, s: Collection<A>): Outcome<Sequence<B>>
    function method max_f<A,B>(a: Collection<A>, key: (A) ~> Outcome<B>): Outcome<A>
    function method sum(a: Collection<nat>): nat

    function method pow(a: nat, b: nat): nat
    function method uint64_new(a: nat): uint64
    function method Bytes1_new(a: nat): Bytes1
    function method Bytes32_new(a: nat): Bytes1
    const Bytes32_default := Bytes32_new(0);
    const boolean_default := 0;
}