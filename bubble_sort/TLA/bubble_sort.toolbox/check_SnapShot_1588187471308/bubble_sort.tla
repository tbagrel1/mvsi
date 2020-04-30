---------------------------- MODULE bubble_sort ----------------------------
EXTENDS TLC, Naturals, Integers, FiniteSets

CONSTANTS tab, n
\*  Init == (* Global variables *)
\*      /\ tab_out = [x \in 0..n - 1 |-> 0]  \* Cheat because of TLA function cell affectation
\*      /\ c = defaultInitValue
\*      /\ d = defaultInitValue
\*      /\ swap = defaultInitValue
\*      /\ pc = "l0"
       


(* --algorithm bubble_sort {
    variables tab_out, c, d, swap;
    
    {
        l0: skip;
        c := 0;
        l1: skip;
        ul1: while (c < n) {
            l2: skip;
            tab_out[c] := tab[c];
            l3: skip;
            c := c + 1;
            l4: skip;
        };
        l5: skip;
        c := 0;
        l6: skip;
        ul2: while (c < (n - 1)) {
            l7: skip;
            d := 0;
            l8: skip;
            ul3: while (d < (n - c - 1)) {
                l9: skip;
                if (tab_out[d] > tab_out[d + 1]) {
                    l10: skip;
                    swap := tab_out[d];
                    l11: skip;
                    tab_out[d] := tab_out[d + 1];
                    l12: skip;
                    tab_out[d + 1] := swap;
                    l13: skip;
                } else {
                    l14: skip;
                };
                l15: skip;
                d := d + 1;
                l16: skip;
            };
            l17: skip;
            c := c + 1;
            l18: skip;
        };
        l19: skip; 
    }
}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4caa2bc1c2c7d4826098453763b061ec
CONSTANT defaultInitValue
VARIABLES tab_out, c, d, swap, pc

vars == << tab_out, c, d, swap, pc >>

Init == (* Global variables *)
        /\ tab_out = [x \in 0..n - 1 |-> 0] \* Cheat because of TLA function cell affectation
        /\ c = defaultInitValue
        /\ d = defaultInitValue
        /\ swap = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ TRUE
      /\ c' = 0
      /\ pc' = "l1"
      /\ UNCHANGED << tab_out, d, swap >>

l1 == /\ pc = "l1"
      /\ TRUE
      /\ pc' = "ul1"
      /\ UNCHANGED << tab_out, c, d, swap >>

ul1 == /\ pc = "ul1"
       /\ IF c < n
             THEN /\ pc' = "l2"
             ELSE /\ pc' = "l5"
       /\ UNCHANGED << tab_out, c, d, swap >>

l2 == /\ pc = "l2"
      /\ TRUE
      /\ tab_out' = [tab_out EXCEPT ![c] = tab[c]]
      /\ pc' = "l3"
      /\ UNCHANGED << c, d, swap >>

l3 == /\ pc = "l3"
      /\ TRUE
      /\ c' = c + 1
      /\ pc' = "l4"
      /\ UNCHANGED << tab_out, d, swap >>

l4 == /\ pc = "l4"
      /\ TRUE
      /\ pc' = "ul1"
      /\ UNCHANGED << tab_out, c, d, swap >>

l5 == /\ pc = "l5"
      /\ TRUE
      /\ c' = 0
      /\ pc' = "l6"
      /\ UNCHANGED << tab_out, d, swap >>

l6 == /\ pc = "l6"
      /\ TRUE
      /\ pc' = "ul2"
      /\ UNCHANGED << tab_out, c, d, swap >>

ul2 == /\ pc = "ul2"
       /\ IF c < (n - 1)
             THEN /\ pc' = "l7"
             ELSE /\ pc' = "l19"
       /\ UNCHANGED << tab_out, c, d, swap >>

l7 == /\ pc = "l7"
      /\ TRUE
      /\ d' = 0
      /\ pc' = "l8"
      /\ UNCHANGED << tab_out, c, swap >>

l8 == /\ pc = "l8"
      /\ TRUE
      /\ pc' = "ul3"
      /\ UNCHANGED << tab_out, c, d, swap >>

ul3 == /\ pc = "ul3"
       /\ IF d < (n - c - 1)
             THEN /\ pc' = "l9"
             ELSE /\ pc' = "l17"
       /\ UNCHANGED << tab_out, c, d, swap >>

l9 == /\ pc = "l9"
      /\ TRUE
      /\ IF tab_out[d] > tab_out[d + 1]
            THEN /\ pc' = "l10"
            ELSE /\ pc' = "l14"
      /\ UNCHANGED << tab_out, c, d, swap >>

l10 == /\ pc = "l10"
       /\ TRUE
       /\ swap' = tab_out[d]
       /\ pc' = "l11"
       /\ UNCHANGED << tab_out, c, d >>

l11 == /\ pc = "l11"
       /\ TRUE
       /\ tab_out' = [tab_out EXCEPT ![d] = tab_out[d + 1]]
       /\ pc' = "l12"
       /\ UNCHANGED << c, d, swap >>

l12 == /\ pc = "l12"
       /\ TRUE
       /\ tab_out' = [tab_out EXCEPT ![d + 1] = swap]
       /\ pc' = "l13"
       /\ UNCHANGED << c, d, swap >>

l13 == /\ pc = "l13"
       /\ TRUE
       /\ pc' = "l15"
       /\ UNCHANGED << tab_out, c, d, swap >>

l14 == /\ pc = "l14"
       /\ TRUE
       /\ pc' = "l15"
       /\ UNCHANGED << tab_out, c, d, swap >>

l15 == /\ pc = "l15"
       /\ TRUE
       /\ d' = d + 1
       /\ pc' = "l16"
       /\ UNCHANGED << tab_out, c, swap >>

l16 == /\ pc = "l16"
       /\ TRUE
       /\ pc' = "ul3"
       /\ UNCHANGED << tab_out, c, d, swap >>

l17 == /\ pc = "l17"
       /\ TRUE
       /\ c' = c + 1
       /\ pc' = "l18"
       /\ UNCHANGED << tab_out, d, swap >>

l18 == /\ pc = "l18"
       /\ TRUE
       /\ pc' = "ul2"
       /\ UNCHANGED << tab_out, c, d, swap >>

l19 == /\ pc = "l19"
       /\ TRUE
       /\ pc' = "Done"
       /\ UNCHANGED << tab_out, c, d, swap >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ ul1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ ul2 \/ l7 \/ l8
           \/ ul3 \/ l9 \/ l10 \/ l11 \/ l12 \/ l13 \/ l14 \/ l15 \/ l16 \/ l17
           \/ l18 \/ l19
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-4d25b6153b55366b8a7bcf13f4869ae7
Range(S) == { S[x] : x \in DOMAIN S }
EulerInd(S) == [m \in Range(tab) |-> IF m \in S THEN 1 ELSE 0 ]
Enum(nn, ttab) == [m \in Range(tab) |-> Cardinality({ ii \in 0..nn - 1 : ttab[ii] = m })]
FuncPM(ff, pp, mm) == [m \in Range(tab) |-> ff[m] + pp[m] - mm[m]]
Forall(S) == S \subseteq { TRUE }
StayInRange(xx) == xx \geq -32768 /\ xx \leq 32767

Types ==
    /\ c \in Int
    /\ d \in Int
    /\ swap \in Int
    
Pl0 ==
    /\ TRUE
Pl1 ==
    /\ c = 0
Pl2 ==
    /\ 0 \leq c /\ c < n /\ 0..c - 1 \subseteq DOMAIN tab_out /\ Enum(c, tab_out) = Enum(c, tab)
Pl3 ==
    /\ 0 \leq c /\ c < n /\ 0..c \subseteq DOMAIN tab_out /\ Enum(c + 1, tab_out) = Enum(c + 1, tab)
Pl4 ==
    /\ 0 \leq c /\ c \leq n /\ 0..c - 1 \subseteq DOMAIN tab_out /\ Enum(c, tab_out) = Enum(c, tab)
Pl5 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
Pl6 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ c = 0 /\ Enum(n, tab_out) = Enum(n, tab)
Pl7 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c..n - 1})
Pl8 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c..n - 1}) /\ d = 0
Pl9 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c..n - 1}) 
    /\ 0 \leq d /\ d < n - c /\ Forall({ tab_out[k] \leq tab_out[d] : k \in 0..d})
Pl10 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c..n - 1}) 
    /\ 0 \leq d /\ d < n - c /\ Forall({ tab_out[k] \leq tab_out[d] : k \in 0..d})
    /\ tab_out[d] > tab_out[d + 1]
Pl11 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) /\ swap \leq tab_out[k] : k \in n - c..n - 1}) 
    /\ 0 \leq d /\ d < n - c /\ Forall({ tab_out[k] \leq tab_out[d] : k \in 0..d})
    /\ tab_out[d] > tab_out[d + 1] /\ swap = tab_out[d] /\ swap > tab_out[d + 1]
Pl12 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 
    /\ Enum(n, tab_out) = FuncPM(Enum(n, tab), EulerInd({ tab_out[d + 1] }), EulerInd({ swap }))
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) /\ swap \leq tab_out[k] : k \in n - c..n - 1}) 
    /\ 0 \leq d /\ d < n - c /\ Forall({ tab_out[k] \leq swap : k \in 0..d + 1})
Pl13 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c..n - 1}) 
    /\ 0 \leq d /\ d < n - c /\ Forall({ tab_out[k] \leq tab_out[d] : k \in 0..d + 1})
Pl14 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c..n - 1}) 
    /\ 0 \leq d /\ d < n - c /\ Forall({ tab_out[k] \leq tab_out[d] : k \in 0..d + 1})
Pl15 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c..n - 1}) 
    /\ 0 \leq d /\ d < n - c /\ Forall({ tab_out[k] \leq tab_out[d] : k \in 0..d + 1}) 
Pl16 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c..n - 1}) 
    /\ 0 \leq d /\ d \leq n - c /\ Forall({ tab_out[k] \leq tab_out[d] : k \in 0..d})
Pl17 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c < n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c - 1..n - 1}) 
Pl18 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c \leq n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ Forall({tab_out[l] \leq tab_out[k] : l \in 0..k }) : k \in n - c..n - 1}) 
Pl19 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ 0 \leq c /\ c \leq n - 1 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2}) 
    
  
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
    /\ pc = "l14" => Pl14
    /\ pc = "l15" => Pl15
    /\ pc = "l16" => Pl16
    /\ pc = "l17" => Pl17
    /\ pc = "l18" => Pl18
    /\ pc = "l19" => Pl19

Pre ==
    /\ n \in Nat
    /\ 0..n - 1 \subseteq DOMAIN tab
Post ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2 })

PartialCorrectness == Pre => (pc = "Done" => Post)
InvOk == Pre => Inv
NoRTE == Pre => (
    /\ StayInRange(d)
    /\ StayInRange(c)
    /\ StayInRange(swap)
)
=============================================================================
\* Modification History
\* Last modified Wed Apr 29 21:09:38 CEST 2020 by alexandre
\* Created Wed Apr 29 18:14:56 CEST 2020 by alexandre
