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
        (forall i: nat :: 0 <= i < currSize ==> conj[i] in Conteudo) &&
        (forall i, j: nat :: 0 <= i < j < currSize ==> conj[i] != conj[j])
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

    method add(x:nat) returns (b:bool)
        requires Invariant()
        modifies conj, Repr
        ensures x in Conteudo
        ensures x >= 0
        ensures Invariant()
        ensures conj.Length == currSize

        ensures b == (x !in old(Conteudo)) 
        
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
