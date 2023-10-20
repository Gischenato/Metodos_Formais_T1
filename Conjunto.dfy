class Conjunto {
    var currSize: nat
    var conj: array<nat>


    ghost var Conteudo: set<nat>
    ghost var Repr: set<object>

    predicate Invariant()
        reads this, Repr, conj
        ensures Invariant() ==> this in Repr
    {
        this in Repr &&
        currSize >= 0 &&
        
        conj.Length == currSize &&

        (currSize == 0 ==> Conteudo == {}) &&
        (currSize  > 0 ==> Conteudo != {}) &&

        (forall i: nat :: i in Conteudo ==> exists j: nat :: 0 <= j < currSize && conj[j] == i) &&
        (forall i: nat :: 0 <= i < currSize ==> conj[i] in Conteudo) &&
        (forall i, j: nat :: 0 <= i < j < conj.Length ==> conj[i] != conj[j])
    }

    
    constructor ()
        ensures Invariant() && fresh(Repr)
        ensures Conteudo == {}
    {
        currSize := 0;
        conj := new nat[0];
        Conteudo := {};
        Repr := {this, conj};
    }

    method isEmpty() returns (b:bool)
        requires Invariant()

        ensures Invariant()
        ensures b == true ==> Conteudo == {}
        ensures b == true ==> conj.Length == 0
        // ensures b == false ==> Conteudo != {}
        // ensures b == false ==> exists i: nat :: i in Conteudo
    {
        b := currSize == 0;
    }

    method size() returns (n:nat)
        requires Invariant()
        ensures Invariant()

        ensures n == currSize == conj.Length 
    {
        n := currSize;
    }


    method contains(x:nat) returns (b:bool)
        requires Invariant()

        ensures Invariant()

        ensures Conteudo == old(Conteudo)
        ensures b == true ==> x in Conteudo
        ensures b == false ==> x !in Conteudo

    {
        var inside := false;
        var i := 0;
        while(i < currSize)
            invariant 0 <= i <= currSize
            invariant forall j: nat :: 0 <= j < i ==> conj[j] != x
        {
            if conj[i] == x {
                inside := true;
                break;
            }
            i := i + 1;
        }
        b := inside;
    }

    method findIdx(x:nat) returns (idx:nat)
        requires Invariant()
        requires x in Conteudo

        ensures Invariant()
        ensures idx < conj.Length && conj[idx] == x
    {
        idx :=0;
        while idx < conj.Length
            invariant 0 <= idx <= conj.Length
            invariant forall i :: 0 <= i < idx ==> conj[i] != x
        {
            if conj[idx]==x
            {
                return;
            }
            idx := idx +  1;
        }
    }

    method remove(x:nat) returns (b:bool)
        requires Invariant()
        modifies conj, Repr
        ensures Invariant()
        ensures x >= 0
        ensures x !in Conteudo


        ensures b == true ==> (x in old(Conteudo))
        ensures b == false ==> (x !in old(Conteudo))

        ensures b == true ==> Conteudo == old(Conteudo) - {x}
        ensures b == false ==> Conteudo == old(Conteudo)

        ensures b == true ==> currSize == old(currSize) - 1
        ensures b == false ==> currSize == old(currSize)
    {
        var inside := this.contains(x);
        if !inside {
            return false;
        }
        var position := this.findIdx(x);
        assert conj[position] == x;
        conj := swap(conj, position, currSize-1);
        assert conj[currSize-1] == x;
        conj := pop(conj);
        Conteudo := Conteudo - {x};
        currSize := currSize - 1;

        assert currSize == conj.Length;
        assert x !in Conteudo;
        assert forall i: nat :: 0 <= i < currSize ==> conj[i] != x;
        assert old(conj[position]) == x;

        return true;
    }

    method add(x:nat) returns (b:bool)
        requires Invariant()
        modifies conj, Repr

        ensures Invariant()
        ensures x >= 0
        
        ensures b == true ==> Conteudo == old(Conteudo) + {x}
        ensures b == false ==> Conteudo == old(Conteudo)

        ensures b == true ==> currSize == old(currSize) + 1
        ensures b == false ==> currSize == old(currSize)

        ensures b == true ==> x !in old(Conteudo)
        ensures b == false ==> x in old(Conteudo)

        ensures exists i: nat :: 0 <= i < conj.Length && conj[i] == x

    {
        var inside := this.contains(x);
        if inside {
            return false;
        }
        assert x !in Conteudo;

        conj := append(conj, x);
        Conteudo := Conteudo + {x};
        currSize := currSize + 1;


        return true;
    }
       
}

method append(arr:array<nat>, n:nat) returns (newArr: array<nat>)
    requires arr.Length >= 0

    ensures newArr.Length == arr.Length + 1
    ensures n >= 0;
    ensures forall i: nat :: 0 <= i < arr.Length ==> newArr[i] == arr[i]
    ensures newArr[newArr.Length-1] == n
    ensures fresh(newArr)
{
    newArr := new nat[arr.Length + 1](x => 0);
    forall v | 0 <= v < arr.Length {
        newArr[v] := arr[v];
    }
    newArr[newArr.Length-1] := n;
}

method pop(arr:array<nat>) returns (newArr: array<nat>)
    requires arr.Length > 0

    ensures newArr.Length == arr.Length - 1
    ensures forall i: nat :: 0 <= i < newArr.Length ==> newArr[i] == arr[i]
    ensures fresh(newArr)
{
    newArr := new nat[arr.Length - 1](x => 0);
    forall v | 0 <= v < newArr.Length {
        newArr[v] := arr[v];
    }
}


method swap(arr:array<nat>, i:nat, j:nat) returns (newArr:array<nat>)
    requires 0 <= i < arr.Length
    requires 0 <= j < arr.Length

    ensures fresh(newArr)
    ensures newArr.Length == arr.Length
    ensures newArr[i] == arr[j] && newArr[j] == arr[i]
    ensures forall k: nat :: 0 <= k < newArr.Length ==> (
        (k == i ==> newArr[k] == arr[j]) && (k == j ==> newArr[k] == arr[i]) && (k != i && k != j ==> newArr[k] == arr[k])
    )
{
    newArr := new nat[arr.Length](x => 0);
    
    forall v | 0 <= v < arr.Length {
        newArr[v] := arr[v];
    }

    newArr[i] := arr[j];
    newArr[j] := arr[i];
}


method Main(){
    var s: set<nat> := {};
    assert s == {};
    assert !(s != {});

    s := s + {1};
    // assert s == {};
    assert s != {};

}