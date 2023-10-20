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

        // (forall i: nat :: i in Conteudo ==> exists j: nat :: 0 <= j < currSize && conj[j] == i) &&
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

    method size() returns (n:nat)
        requires Invariant()
        ensures Invariant()


    {
        n := currSize;
    }


    method contains(x:nat) returns (b:bool)
        requires Invariant()

        ensures Invariant()

        ensures Conteudo == old(Conteudo)
        ensures b == true ==> x in Conteudo && b == false ==> x !in Conteudo

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

    method remove(x:nat) returns (b:bool)
        requires Invariant()
        modifies conj, Repr
        ensures Invariant()
        ensures x >= 0
        ensures x !in Conteudo

        ensures Conteudo == old(Conteudo) - {x}
        
        ensures forall i: nat :: 0 <= i < conj.Length ==> conj[i] != x

        ensures b == true ==> (x in old(Conteudo)) && b == false ==> (x !in old(Conteudo))
        ensures b == true ==> Conteudo == old(Conteudo) - {x}
        ensures b == true ==> currSize == old(currSize) - 1
        ensures b == false ==> currSize == old(currSize)

    {
        
        var i := 0;
        while(i < currSize)
        invariant 0 <= i <= currSize
        invariant forall j: nat :: 0 <= j < i ==> conj[j] != x
        {
            if conj[i] == x {

                var newArr := new nat[currSize - 1](j => 0);

                conj[i] := conj[currSize - 1];

                forall j | 0 <= j < currSize - 1 {                    
                    newArr[j] := conj[j];
                }

                currSize := currSize - 1;
                conj := newArr;

                Conteudo := Conteudo - {x};

                return true;
            }
            i := i + 1;
        }
        // assert forall j: nat :: j in Conteudo ==> (exists k: nat :: 0 <= k < currSize && conj[k] == j
        assert forall j: nat :: 0 <= j < currSize ==> conj[j] != x;

        Conteudo := Conteudo - {x};
        return false;
    }

    method add(x:nat) returns (b:bool)
        requires Invariant()
        modifies conj, Repr
        ensures x in Conteudo
        ensures x >= 0
        ensures Invariant()
        ensures conj.Length == currSize

        ensures Conteudo == old(Conteudo) + {x}

        ensures b == true ==> (x !in old(Conteudo)) && b == false ==> (x in old(Conteudo))
        ensures b == true ==> Conteudo == old(Conteudo) + {x}
        ensures b == false ==> Conteudo == old(Conteudo)
        ensures b == true ==> currSize == old(currSize) + 1
        ensures b == false ==> currSize == old(currSize)
    {
        var i := 0;
        
        while(i < currSize) 
        invariant 0 <= i <= currSize
        invariant forall j: nat :: 0 <= j < i ==> conj[j] != x
        {
            if conj[i] == x {
                b := false;
                return false;
            }
            i := i + 1;
        }
        b := true;


        var newArr := new nat[currSize + 1](j => 0);

        forall v | 0 <= v < currSize {
            newArr[v] := conj[v];
        }
        newArr[currSize] := x;


        currSize := currSize + 1;
        conj := newArr;


        Conteudo := Conteudo + {x};
        return true;
    }
       
}
