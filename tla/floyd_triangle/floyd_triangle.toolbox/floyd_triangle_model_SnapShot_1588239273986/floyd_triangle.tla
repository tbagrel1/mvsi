------------------------------ MODULE floyd_triangle ------------------------------

EXTENDS TLC, Naturals, Integers, FiniteSets

CONSTANTS n

(* 
--algorithm shell_sort {
    variables u, v, i, a, c, display;
    {
        l0: skip;
        u := 0;
        v := 0;
        l1: skip;
        i := 1;
        l2: skip;
        a := 1;
        l3: skip;
        ul1: while (i <= n) {
            l4: skip;
            c := 1;
            l5: skip;
            ul2: while (c <= i) { 
                l6: skip;
                display[<<u, v>>] := a;
                v := v + 1;
                l7: skip;
                a := a + 1;
                l8: skip;
                c := c + 1;
                l9: skip;
            };
            l10: skip;
            u := u + 1;
            v := 0;
            l11: skip;
            i := i + 1;
            l12: skip;
        };
        l13: skip;
    }
}
end algorithm*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES u, v, i, a, c, display, pc

vars == << u, v, i, a, c, display, pc >>

Init == (* Global variables *)
        /\ u = defaultInitValue
        /\ v = defaultInitValue
        /\ i = defaultInitValue
        /\ a = defaultInitValue
        /\ c = defaultInitValue
        /\ display = [<<x, y>> \in (0..n-1) \X (0..n-1) |-> 0]
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ TRUE
      /\ u' = 0
      /\ v' = 0
      /\ pc' = "l1"
      /\ UNCHANGED << i, a, c, display >>

l1 == /\ pc = "l1"
      /\ TRUE
      /\ i' = 1
      /\ pc' = "l2"
      /\ UNCHANGED << u, v, a, c, display >>

l2 == /\ pc = "l2"
      /\ TRUE
      /\ a' = 1
      /\ pc' = "l3"
      /\ UNCHANGED << u, v, i, c, display >>

l3 == /\ pc = "l3"
      /\ TRUE
      /\ pc' = "ul1"
      /\ UNCHANGED << u, v, i, a, c, display >>

ul1 == /\ pc = "ul1"
       /\ IF i <= n
             THEN /\ pc' = "l4"
             ELSE /\ pc' = "l13"
       /\ UNCHANGED << u, v, i, a, c, display >>

l4 == /\ pc = "l4"
      /\ TRUE
      /\ c' = 1
      /\ pc' = "l5"
      /\ UNCHANGED << u, v, i, a, display >>

l5 == /\ pc = "l5"
      /\ TRUE
      /\ pc' = "ul2"
      /\ UNCHANGED << u, v, i, a, c, display >>

ul2 == /\ pc = "ul2"
       /\ IF c <= i
             THEN /\ pc' = "l6"
             ELSE /\ pc' = "l10"
       /\ UNCHANGED << u, v, i, a, c, display >>

l6 == /\ pc = "l6"
      /\ TRUE
      /\ PrintT(a)
      /\ display' = [display EXCEPT ![<<u, v>>] = a]
      /\ v' = v + 1
      /\ pc' = "l7"
      /\ UNCHANGED << u, i, a, c >>

l7 == /\ pc = "l7"
      /\ TRUE
      /\ a' = a + 1
      /\ pc' = "l8"
      /\ UNCHANGED << u, v, i, c, display >>

l8 == /\ pc = "l8"
      /\ TRUE
      /\ c' = c + 1
      /\ pc' = "l9"
      /\ UNCHANGED << u, v, i, a, display >>

l9 == /\ pc = "l9"
      /\ TRUE
      /\ pc' = "ul2"
      /\ UNCHANGED << u, v, i, a, c, display >>

l10 == /\ pc = "l10"
       /\ TRUE
       /\ u' = u + 1
       /\ v' = 0
       /\ PrintT("------------------------")
       /\ pc' = "l11"
       /\ UNCHANGED << i, a, c, display >>

l11 == /\ pc = "l11"
       /\ TRUE
       /\ i' = i + 1
       /\ pc' = "l12"
       /\ UNCHANGED << u, v, a, c, display >>

l12 == /\ pc = "l12"
       /\ TRUE
       /\ pc' = "ul1"
       /\ UNCHANGED << u, v, i, a, c, display >>

l13 == /\ pc = "l13"
       /\ TRUE
       /\ pc' = "Done"
       /\ UNCHANGED << u, v, i, a, c, display >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ ul1 \/ l4 \/ l5 \/ ul2 \/ l6 \/ l7 \/ l8
           \/ l9 \/ l10 \/ l11 \/ l12 \/ l13
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

Forall(S) == S \subseteq { TRUE }
StayInRange(xx) == xx \geq -32768 /\ xx \leq 32767

Types ==
    /\ u \in Nat
    /\ v \in Nat
    /\ i \in Nat
    /\ c \in Nat
    /\ a \in Nat
    /\ i \in Nat
    
Pl0 ==
    /\ TRUE
Pl1 ==
    /\ u = 0 /\ v = 0
Pl2 ==
    /\ i = 1 /\ u = i - 1 /\ v = 0
Pl3 ==
    i = 1 /\ a = 1 /\ u = i - 1 /\ v = 0
Pl4 ==
    /\ i \in 1..n /\ a = (((i-1)*i)\div 2) + 1 /\ u = i - 1 /\ v = 0
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..i-2 })
Pl5 ==
    /\ i \in 1..n /\ c = 1 /\ a = (((i-1)*i)\div 2) + c /\ u = i - 1 /\ v = c - 1
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..i-2 })
Pl6 ==
    /\ i \in 1..n /\ c \in 1..i /\ a = (((i-1)*i)\div 2) + c /\ u = i - 1 /\ v = c - 1
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..i-2 })
    /\ Forall({ (<<i-1,x>> \in DOMAIN display /\ display[<<i-1,x>>] = ((i-1)*i)\div 2 + x + 1) : x \in 0..c-2 })
Pl7 ==
    /\ i \in 1..n /\ c \in 1..i /\ a = (((i-1)*i)\div 2) + c /\ u = i - 1 /\ v = c
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..i-2 })
    /\ Forall({ (<<i-1,x>> \in DOMAIN display /\ display[<<i-1,x>>] = ((i-1)*i)\div 2 + x + 1) : x \in 0..c-1 })
Pl8 ==
    /\ i \in 1..n /\ c \in 1..i /\ a = (((i-1)*i)\div 2) + c + 1 /\ u = i - 1 /\ v = c
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..i-2 })
    /\ Forall({ (<<i-1,x>> \in DOMAIN display /\ display[<<i-1,x>>] = ((i-1)*i)\div 2 + x + 1) : x \in 0..c-1 })
Pl9 ==
    /\ i \in 1..n /\ c \in 1..i+1 /\ a = (((i-1)*i)\div 2) + c /\ u = i - 1 /\ v = c-1
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..i-2 })
    /\ Forall({ (<<i-1,x>> \in DOMAIN display /\ display[<<i-1,x>>] = ((i-1)* i)\div 2 + x + 1) : x \in 0..c-2 })
Pl10 ==
    /\ i \in 1..n /\ c = i + 1 /\ a = (((i+1)*i)\div 2) + 1 /\ u = i - 1 /\ v = c-1
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..i-1 })
Pl11 ==
    /\ i \in 1..n /\ c = i + 1 /\ a = (((i+1)*i)\div 2) + 1 /\ u = i /\ v = 0
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..i-1 })
Pl12 ==
    /\ i \in 1..n+1 /\ c = i /\ a = (((i-1)*i)\div 2) + 1 /\ u = i - 1 /\ v = 0
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..i-2 })
Pl13 ==
    /\ i = n + 1 /\ c = i /\ a = (((i-1)*i)\div 2) + 1 /\ u = i - 1 /\ v = 0
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..n-1 })

Inv ==
    /\ Types
    /\ pc = "l0" => Pl0
    /\ pc = "l1" => Pl1
    /\ pc = "l2" => Pl2
    /\ pc = "l3" => Pl3
    /\ pc = "l4" => Pl4
    /\ pc = "l5" => Pl5
    /\ pc = "l6" => Pl6
    /\ pc = "l7" => Pl7
    /\ pc = "l8" => Pl8
    /\ pc = "l9" => Pl9
    /\ pc = "l10" => Pl10
    /\ pc = "l11" => Pl11
    /\ pc = "l12" => Pl12
    /\ pc = "l13" => Pl13
     
Pre ==
    /\ n \in Nat

Post ==
    /\ Forall({ Forall({ (<<j,k>> \in DOMAIN display /\ display[<<j,k>>] = (j*(j+1))\div 2 + k + 1) : k \in 0..j }) : j \in 0..n-1 })

PartialCorrectness == Pre => (pc = "Done" => Post)
InvOk == Pre => (Inv)
NoRTE == Pre => (
    /\ StayInRange(u)
    /\ StayInRange(v)
    /\ StayInRange(i)
    /\ StayInRange(c)
    /\ StayInRange(a)
)

=============================================================================
