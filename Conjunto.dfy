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

    method addArray(arr: array<nat>) returns (qnt: nat, newValues: set<nat>)
        requires Invariant()
        modifies Repr

        ensures Invariant()
        ensures currSize == old(currSize) + qnt
        ensures Conteudo == old(Conteudo) + newValues
        ensures forall i: nat :: 0 <= i < arr.Length ==> arr[i] in Conteudo
        ensures forall i: nat :: i in Conteudo ==> exists j: nat :: 0 <= j < currSize && conj[j] == i
        ensures forall i: nat :: !(exists k : nat :: 0 <= k < arr.Length && arr[k] == i) ==> i !in newValues
    {
        // assert 1 == 0;
        var toAdd: set<nat> := {};
        var i := 0;
        var total := 0;
        
        while(i < arr.Length)
            invariant 0 <= i <= arr.Length
            invariant Invariant()
            invariant forall j: nat :: 0 <= j < i ==> arr[j] in Conteudo
            invariant forall j: nat :: 0 <= j < i ==> exists k: nat :: 0 <= k < currSize && conj[k] == arr[j]
            invariant forall j: nat :: j in Conteudo ==> exists k: nat :: 0 <= k < currSize && conj[k] == j
            invariant currSize == old(currSize) + total
            invariant Conteudo == old(Conteudo) + toAdd
            invariant forall j: nat :: 0 <= j < i ==> arr[j] in toAdd
            invariant forall j: nat :: j in toAdd ==> exists k : nat :: 0 <= k < i && arr[k] == j
            
        {
            var value := arr[i];
            toAdd := toAdd + {arr[i]};
            var inside := this.contains(value);
            if inside {
                i := i + 1;
                continue;
            }
            total := total + 1;
            conj := append(conj, value);
            Conteudo := Conteudo + {value};
            currSize := currSize + 1;
            i := i + 1;
        }


        assert currSize == old(currSize) + total;
        return total, toAdd;

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
}

method Main2(){
    var conjunto := new Conjunto();
    
    var size := conjunto.size();
    assert size == 0;

    var empty := conjunto.isEmpty();
    assert empty == true;

    var inserir := conjunto.add(2);
    assert inserir == true;

    empty := conjunto.isEmpty();
    assert empty == false;

    assert conjunto.Conteudo == {2};

    
    var arr := new nat[5](x => x*5); // 0, 5, 10, 15, 20
    assert 2 in conjunto.Conteudo;
    assert 6 !in conjunto.Conteudo;

    var qnt, s := conjunto.addArray(arr);
    
    assert arr[1] == 5;
    assert arr[1] in conjunto.Conteudo;
    assert arr[0] == 0;
    assert arr[0] in conjunto.Conteudo;
    assert 0 in conjunto.Conteudo;
    assert 5 in conjunto.Conteudo;
    assert 6 !in conjunto.Conteudo;
    assert 2 in conjunto.Conteudo;

    assert forall i: nat :: 0 <= i < arr.Length ==> arr[i] in conjunto.Conteudo;

    // var remove := conjunto.remove(5);
    // Por algum motivo, o assert abaixo nao funciona
    // nao entendi o porque, ja que depois ele funciona
    // assert 10 in conjunto.Conteudo;
    assert arr[2] == 10;
    assert arr[2] in conjunto.Conteudo;
    assert 10 in conjunto.Conteudo;
    

}