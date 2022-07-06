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
    method a_<T>(r: (Status, T)) returns (status_: Status, ret_: T) {
        ret_ :- r.0, r.1;
    }

    datatype FStatus<T> =
    | FSuccess(value: T)
    | FFailure
    {
        predicate method IsFailure() { this.FFailure?  }
        function method Extract(): T
            requires !IsFailure()
        {
            this.value
        }
        function method PropagateFailure(): FStatus<T>
            requires IsFailure()
        {
            FFailure
        }
    }
    method b_<T>(f: FStatus<T>, default: T) returns (status_: Status, ret_: T) {
        if f.IsFailure() {
            return Failure, default;
        } else {
            return Success, f.Extract();
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
        function method has_next(): bool
        method next() returns (ret_: T) modifies this

    }
    trait Collection<T> {
        function method contains(k: T): bool
    }
    trait Sequence<T> extends Collection<T> {
        function method get(k: nat): (Status, T)
        function method get_nf(i: nat): T
    }
    class Dict<K,V> {
        function method keys(): Sequence<K>
        function method contains(k: K): bool
        function method get(k: K): (Status, V)
        function method get_nf(k: K): V requires contains(k)
        method set_value(k: K, v: V)
    }
    class Set<T> extends Collection<T> {
        constructor empty() {}
        constructor(t: seq<T>) {}
        function method contains(k: T): bool
        function method intersection(s: Sequence<T>): Set<T>
        method add(e: T) modifies this
    }
    class PyList<T> extends Sequence<T> {
        constructor empty() {}
        constructor(t: seq<T>) {}
        function method contains(k: T): bool
        function method get(k: nat): (Status, T)
        function method get_nf(i: nat): T
        method append(e: T) modifies this
    }
    class ssz_List<T> extends Sequence<T> {
        function method contains(k: T): bool
        function method get(k: nat): (Status, T)
        function method get_nf(i: nat): T
    }
    class ssz_Vector<T> extends Sequence<T> {
        function method contains(k: T): bool
        function method get(k: nat): (Status, T)
        function method get_nf(i: nat): T
    }
    type Bitlist = ssz_List<boolean>
    type Bitvector = ssz_Vector<boolean>

    function method hash(a: nat): Bytes32
    function method hash_tree_root<T>(a: T): Bytes32

    function method iter<T>(a: Collection<T>): Iterator<T>
    function method has_next<T>(a: Iterator<T>): bool {
        a.has_next()
    }
    method next<T>(a: Iterator<T>)
    returns (ret_: T)
    modifies a
    {
        ret_ := a.next();
    }

    function method len<T>(a: Collection<T>): nat
    function method seq_get<T>(a: Sequence<T>, i: nat): T

    function method pyassert(b: bool): Status
    ensures b <==> pyassert(b).Success?
    ensures !b <==> pyassert(b).Failure?
    {
      if b then Success else Failure
    }

    function method Bitlist_new(a: seq<bool>): Bitlist
    function method Bitvector_new(): Bitvector
    function method Dict_new<K,V>(a: seq<(K,V)>): Dict<K,V>
    function method PyList_empty<T>(): PyList<T> { PyList_new([]) }
    function method PyList_new<T>(a: seq<T>): PyList<T>
    function method Set_empty<T>(): Set<T> { Set_new([]) }
    function method Set_new<T>(a: seq<T>): Set<T>
    function method List_new<T>(a: seq<T>): ssz_List<T>
    function method Vector_new<T>(): ssz_Vector<T>

    function method pylist<T>(s: Collection<T>): PyList<T>
    function method pyset<T>(s: Collection<T>): Set<T>
    function method any<T>(s: Sequence<T>): bool
    function method all<T>(s: Sequence<T>): bool

    function method filter<T>(f: (T) -> bool, s: Collection<T>): Sequence<T>
    function method filter_f<T>(f: (T) -> (Status, bool), s: Collection<T>): (Status, Sequence<T>)
    function method pymap<A,B>(f: (A) -> B, s: Collection<A>): Sequence<B>
    function method max<A,B>(a: Collection<A>, key: (A) -> B): (Status, A)
    function method sum(a: Collection<nat>): nat

    function method pow(a: nat, b: nat): nat
    function method uint64_new(a: nat): uint64
    function method Bytes1_new(a: nat): Bytes1
    function method Bytes32_new(a: nat): Bytes1
    const Bytes32_default := Bytes32_new(0);
    const boolean_default := 0;
}