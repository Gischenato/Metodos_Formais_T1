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

        (forall i: nat :: i in Conteudo ==> exists j: nat :: 0 <= j < currSize && conj[j] == i) &&
        (forall i: nat :: 0 <= i < currSize ==> conj[i] in Conteudo) &&
        (forall i, j: nat :: 0 <= i < j < conj.Length ==> conj[i] != conj[j])
    }

    
    constructor ()
        ensures Invariant() && fresh(Repr)
        ensures Conteudo == {}
        ensures currSize == 0
        ensures conj.Length == 0
    {
        currSize := 0;
        conj := new nat[0];
        Conteudo := {};
        Repr := {this, conj};
    }

    method isEmpty() returns (b:bool)
        requires Invariant()

        ensures Invariant()
        ensures currSize == 0 ==> Conteudo == {}
        ensures currSize == 0 ==> b == true
        ensures currSize > 0 ==> b == false
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
        modifies Repr
        ensures Invariant() && fresh(Repr - old(Repr))
        ensures x >= 0
        ensures x !in Conteudo

        ensures b == true ==> (x in old(Conteudo))
        ensures b == false ==> (x !in old(Conteudo))

        ensures b == true ==> Conteudo == old(Conteudo) - {x}
        ensures b == false ==> Conteudo == old(Conteudo)

        ensures b == true ==> currSize == old(currSize) - 1
        ensures b == false ==> currSize == old(currSize)
    {
        var tamanho := this.size();
        var inside := this.contains(x);
        if !inside {
            return false;
        }
        var position := this.findIdx(x);
        assert conj[position] == x;
        conj := swap(conj, position, currSize-1);
        assert currSize > 0 ==> Conteudo != {};
        assert conj[currSize-1] == x;
        conj := pop(conj);
        currSize := currSize - 1;
        Conteudo := Conteudo - {x};
        // assert currSize > 0 ==> Conteudo != {};

        assert currSize == conj.Length;
        assert x !in Conteudo;
        assert forall i: nat :: 0 <= i < currSize ==> conj[i] != x;
        assert old(conj[position]) == x;

        assert forall i: nat :: 0 <= i < currSize ==> conj[i] in Conteudo;
        assert forall i: nat :: i in Conteudo ==> exists j: nat :: 0 <= j < currSize && conj[j] == i;
        assert currSize == 0 ==> Conteudo == {};
        assert currSize > 0 ==> forall i: nat :: i in Conteudo ==> exists j: nat :: 0 <= j < currSize && conj[j] == i;

        return true;
    }

    method addArray(arr: array<nat>)
        requires Invariant()
        requires arr.Length > 0
        modifies Repr
        ensures Invariant() && fresh(Repr - old(Repr))
        // ensures forall i: nat :: 0 <= i < arr.Length ==> exists j: nat :: 0 <= j < currSize && conj[j] == arr[i]

    {
        assume conj != arr;

        var size := arr.Length;
        var newArr := arr[..];
        // var teste := newArr[0];

        var value := arr[0];
        assert newArr[0] == arr[0];
        var i := 0;
        while(i < size)
            invariant 0 <= i <= size
            invariant Invariant() && fresh(Repr - old(Repr))
            // invariant Conteudo == old(Conteudo) + {arr[i]}
            modifies Repr
            // invariant i < size ==> newArr[i] == arr[i]
            // invariant forall j: nat :: 0 <= j < i ==> newArr[j] in Conteudo
        {
            var value := arr[i];
            var test := value;
            // var test := value;
            // assert newArr[0] == arr[0];
            assert value == arr[i];
            var insert := this.add(value);
            assert test == value;
            assert value == arr[i];
            assert arr[i] in Conteudo;
            i := i + 1;
        }
        // assert forall j: nat :: 0 <= j < arr.Length ==> exists k: nat :: 0 <= k < currSize && conj[k] == arr[j];
    }

    method add(x:nat) returns (b:bool)
        requires Invariant()
        modifies Repr

        ensures Invariant() && fresh(Repr - old(Repr))
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
    var conjunto := new Conjunto();
    var size := conjunto.size();
    assert size == 0;

    var empty := conjunto.isEmpty();
    assert empty == true;

    var inserir := conjunto.add(67);
    assert inserir == true;

    empty := conjunto.isEmpty();
    assert empty == false;
    
    var remover := conjunto.remove(67);
    assert remover == true;

    empty := conjunto.isEmpty();
    assert empty == true;

    remover := conjunto.remove(67);
    assert remover == false;

    inserir := conjunto.add(1);
    assert inserir == true;
    inserir := conjunto.add(4);
    assert inserir == true;
    inserir := conjunto.add(4);
    assert inserir == false;
    inserir := conjunto.add(6);
    assert inserir == true;
    inserir := conjunto.add(7);
    assert inserir == true;
    inserir := conjunto.add(9);
    assert inserir == true;
    inserir := conjunto.add(10);
    assert inserir == true;
    inserir := conjunto.add(15);
    assert inserir == true;
    inserir := conjunto.add(10);
    assert inserir == false;

    size := conjunto.size();
    assert size == 7;

    assert conjunto.Conteudo == {1, 4, 6, 7, 9, 10, 15};
    
    remover := conjunto.remove(6);
    assert remover == true;
    remover := conjunto.remove(15);
    assert remover == true;
    remover := conjunto.remove(10);
    assert remover == true;

    size := conjunto.size();
    assert size == 4;

    assert conjunto.Conteudo == {1, 4, 7, 9};

    var arr := new nat[5](x => x*5); // 0, 5, 10, 15, 20
    conjunto.addArray(arr);

    // assert conjunto.Conteudo == {1, 4, 7, 9, 0, 5, 10, 15, 20};
    size := conjunto.size();
    assert size == 9;
}