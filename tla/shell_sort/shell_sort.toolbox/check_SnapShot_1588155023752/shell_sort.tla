----------------------------- MODULE shell_sort -----------------------------

EXTENDS TLC, Naturals, Integers, FiniteSets

CONSTANTS tab, n

(* --algorithm shell_sort {
    variables tab_out, i, j, inc, tmp;
    {
        l0: skip;
        i := 0;
        l1: skip;
        ul1: while (i < n) {
            l2: skip;
            tab_out[i] := tab[i];
            l3: skip;
            i := i + 1;
            l4: skip;
        };
        l5: skip;
        inc := 3;
        l6: skip;
        ul2: while (inc > 0) { 
            l7: skip;
            i := 0;
            l8: skip;
            ul3: while (i < n) {
                l9: skip;
                j := i;
                l10: skip;
                tmp := tab_out[i];
                l11: skip;
                ul4: while ((j >= inc) /\ (tab_out[j - inc] > tmp)) { 
                    l12: skip;
                    tab_out[j] := tab_out[j - inc];
                    l13: skip;
                    j := j - inc;
                    l14: skip;
                };
                l15: skip;
                tab_out[j] := tmp;
                l16: skip;
                i := i + 1;
                l17: skip;
            };
            l18: skip;
            if (inc \div 2 # 0) {
                l19: skip;
                inc := inc \div 2;
                l20: skip;
            } else {
                l21: skip;
                if (inc = 1) {
                    l22: skip;
                    inc := 0;
                    l23: skip;
                } else {
                    l24: skip;
                    inc := 1;
                    l25: skip;
                };
                l26: skip;
            };
            l27: skip;
        };
        l28: skip;
    }
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES tab_out, i, j, inc, tmp, pc

vars == << tab_out, i, j, inc, tmp, pc >>

Init == (* Global variables *)
        /\ tab_out = [x \in 0..n - 1 |-> 0]  \* Cheat because of TLA function cell affectation
        /\ i = defaultInitValue
        /\ j = defaultInitValue
        /\ inc = defaultInitValue
        /\ tmp = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ TRUE
      /\ i' = 0
      /\ pc' = "l1"
      /\ UNCHANGED << tab_out, j, inc, tmp >>

l1 == /\ pc = "l1"
      /\ TRUE
      /\ pc' = "ul1"
      /\ UNCHANGED << tab_out, i, j, inc, tmp >>

ul1 == /\ pc = "ul1"
       /\ IF i < n
             THEN /\ pc' = "l2"
             ELSE /\ pc' = "l5"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l2 == /\ pc = "l2"
      /\ TRUE
      /\ tab_out' = [tab_out EXCEPT ![i] = tab[i]]
      /\ pc' = "l3"
      /\ UNCHANGED << i, j, inc, tmp >>

l3 == /\ pc = "l3"
      /\ TRUE
      /\ i' = i + 1
      /\ pc' = "l4"
      /\ UNCHANGED << tab_out, j, inc, tmp >>

l4 == /\ pc = "l4"
      /\ TRUE
      /\ pc' = "ul1"
      /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l5 == /\ pc = "l5"
      /\ TRUE
      /\ inc' = 3
      /\ pc' = "l6"
      /\ UNCHANGED << tab_out, i, j, tmp >>

l6 == /\ pc = "l6"
      /\ TRUE
      /\ pc' = "ul2"
      /\ UNCHANGED << tab_out, i, j, inc, tmp >>

ul2 == /\ pc = "ul2"
       /\ IF inc > 0
             THEN /\ pc' = "l7"
             ELSE /\ pc' = "l28"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l7 == /\ pc = "l7"
      /\ TRUE
      /\ i' = 0
      /\ pc' = "l8"
      /\ UNCHANGED << tab_out, j, inc, tmp >>

l8 == /\ pc = "l8"
      /\ TRUE
      /\ pc' = "ul3"
      /\ UNCHANGED << tab_out, i, j, inc, tmp >>

ul3 == /\ pc = "ul3"
       /\ IF i < n
             THEN /\ pc' = "l9"
             ELSE /\ pc' = "l18"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l9 == /\ pc = "l9"
      /\ TRUE
      /\ j' = i
      /\ pc' = "l10"
      /\ UNCHANGED << tab_out, i, inc, tmp >>

l10 == /\ pc = "l10"
       /\ TRUE
       /\ tmp' = tab_out[i]
       /\ pc' = "l11"
       /\ UNCHANGED << tab_out, i, j, inc >>

l11 == /\ pc = "l11"
       /\ TRUE
       /\ pc' = "ul4"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

ul4 == /\ pc = "ul4"
       /\ IF (j >= inc) /\ (tab_out[j - inc] > tmp)
             THEN /\ pc' = "l12"
             ELSE /\ pc' = "l15"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l12 == /\ pc = "l12"
       /\ TRUE
       /\ tab_out' = [tab_out EXCEPT ![j] = tab_out[j - inc]]
       /\ pc' = "l13"
       /\ UNCHANGED << i, j, inc, tmp >>

l13 == /\ pc = "l13"
       /\ TRUE
       /\ j' = j - inc
       /\ pc' = "l14"
       /\ UNCHANGED << tab_out, i, inc, tmp >>

l14 == /\ pc = "l14"
       /\ TRUE
       /\ pc' = "ul4"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l15 == /\ pc = "l15"
       /\ TRUE
       /\ tab_out' = [tab_out EXCEPT ![j] = tmp]
       /\ pc' = "l16"
       /\ UNCHANGED << i, j, inc, tmp >>

l16 == /\ pc = "l16"
       /\ TRUE
       /\ i' = i + 1
       /\ pc' = "l17"
       /\ UNCHANGED << tab_out, j, inc, tmp >>

l17 == /\ pc = "l17"
       /\ TRUE
       /\ pc' = "ul3"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l18 == /\ pc = "l18"
       /\ TRUE
       /\ IF inc \div 2 # 0
             THEN /\ pc' = "l19"
             ELSE /\ pc' = "l21"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l19 == /\ pc = "l19"
       /\ TRUE
       /\ inc' = (inc \div 2)
       /\ pc' = "l20"
       /\ UNCHANGED << tab_out, i, j, tmp >>

l20 == /\ pc = "l20"
       /\ TRUE
       /\ pc' = "l27"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l21 == /\ pc = "l21"
       /\ TRUE
       /\ IF inc = 1
             THEN /\ pc' = "l22"
             ELSE /\ pc' = "l24"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l22 == /\ pc = "l22"
       /\ TRUE
       /\ inc' = 0
       /\ pc' = "l23"
       /\ UNCHANGED << tab_out, i, j, tmp >>

l23 == /\ pc = "l23"
       /\ TRUE
       /\ pc' = "l26"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l24 == /\ pc = "l24"
       /\ TRUE
       /\ inc' = 1
       /\ pc' = "l25"
       /\ UNCHANGED << tab_out, i, j, tmp >>

l25 == /\ pc = "l25"
       /\ TRUE
       /\ pc' = "l26"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l26 == /\ pc = "l26"
       /\ TRUE
       /\ pc' = "l27"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l27 == /\ pc = "l27"
       /\ TRUE
       /\ pc' = "ul2"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

l28 == /\ pc = "l28"
       /\ TRUE
       /\ pc' = "Done"
       /\ UNCHANGED << tab_out, i, j, inc, tmp >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ ul1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ ul2 \/ l7 \/ l8
           \/ ul3 \/ l9 \/ l10 \/ l11 \/ ul4 \/ l12 \/ l13 \/ l14 \/ l15 \/ l16
           \/ l17 \/ l18 \/ l19 \/ l20 \/ l21 \/ l22 \/ l23 \/ l24 \/ l25 \/ l26
           \/ l27 \/ l28
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

Range(S) == { S[x] : x \in DOMAIN S }
EulerInd(S) == [m \in Range(tab) |-> IF m \in S THEN 1 ELSE 0 ]
Enum(nn, ttab) == [m \in Range(tab) |-> Cardinality({ ii \in 0..nn - 1 : ttab[ii] = m })]
FuncPM(ff, pp, mm) == [m \in Range(tab) |-> ff[m] + pp[m] - mm[m]]
Forall(S) == S \subseteq { TRUE }
StayInRange(xx) == xx \geq -32768 /\ xx \leq 32767

Types ==
    /\ i \in Int
    /\ j \in Int
    /\ inc \in Int
    /\ tmp \in Int
Pl0 ==
    /\ TRUE
Pl1 ==
    /\ i = 0
Pl2 ==
    /\ 0 \leq i /\ i < n /\ 0..i - 1 \subseteq DOMAIN tab_out /\ Enum(i, tab_out) = Enum(i, tab)
Pl3 ==
    /\ 0 \leq i /\ i < n /\ 0..i \subseteq DOMAIN tab_out /\ Enum(i + 1, tab_out) = Enum(i + 1, tab)
Pl4 ==
    /\ 0 \leq i /\ i \leq n /\ 0..i - 1 \subseteq DOMAIN tab_out /\ Enum(i, tab_out) = Enum(i, tab)
Pl5 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
Pl6 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc = 3 /\ Enum(n, tab_out) = Enum(n, tab)
Pl7 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ Enum(n, tab_out) = Enum(n, tab)
Pl8 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ i = 0 /\ Enum(n, tab_out) = Enum(n, tab)
Pl9 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ 0 \leq i /\ i < n /\ Enum(n, tab_out) = Enum(n, tab)
    /\ (inc = 1 => Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..i - 2 }))
Pl10 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ 0 \leq i /\ i < n /\ Enum(n, tab_out) = Enum(n, tab)
    /\ (inc = 1 => Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..i - 2 })) /\ j = i
Pl11 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ 0 \leq i /\ i < n /\ Enum(n, tab_out) = Enum(n, tab)
    /\ (inc = 1 => Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..i - 2 })) /\ j = i
    /\ tmp = tab_out[i]
Pl12 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ 0 \leq i /\ i < n
    /\ inc \leq j /\ j \leq i /\ tab_out[j - inc] \geq tmp
    /\ Enum(n, tab_out) = FuncPM(Enum(n, tab), EulerInd({ tab_out[j] }), EulerInd({ tmp }))
    /\ (inc = 1 => (Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..i - 2 }) /\ (j = i \/ tab_out[i - 1] \leq tab_out[i])))
Pl13 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ 0 \leq i /\ i < n
    /\ inc \leq j /\ j \leq i /\ tab_out[j - inc] \geq tmp
    /\ Enum(n, tab_out) = FuncPM(Enum(n, tab), EulerInd({ tab_out[j - inc] }), EulerInd({ tmp }))
    /\ (inc = 1 => Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..i - 1 }))
Pl14 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ 0 \leq i /\ i < n
    /\ 0 \leq j /\ j \leq i - 1 /\ tab_out[j] \geq tmp
    /\ Enum(n, tab_out) = FuncPM(Enum(n, tab), EulerInd({ tab_out[j] }), EulerInd({ tmp }))
    /\ (inc = 1 => Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..i - 1 }))
Pl15 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ 0 \leq i /\ i < n
    /\ 0 \leq j /\ j < n /\ tab_out[j] \geq tmp
    /\ Enum(n, tab_out) = FuncPM(Enum(n, tab), EulerInd({ tab_out[j] }), EulerInd({ tmp }))
    /\ (inc = 1 => (Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..i - 1 }) /\ Forall({ tab_out[k] \leq tmp : k \in 0..j - 1 })))
Pl16 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ 0 \leq i /\ i < n
    /\ Enum(n, tab_out) = Enum(n, tab)
    /\ (inc = 1 => Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..i - 1 }))
Pl17 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ 0 \leq i /\ i \leq n
    /\ Enum(n, tab_out) = Enum(n, tab)
    /\ (inc = 1 => Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..i - 2 }))
Pl18 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc > 0 /\ Enum(n, tab_out) = Enum(n, tab)
    /\ (inc = 1 => Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2 }))
Pl19 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc \geq 2 /\ Enum(n, tab_out) = Enum(n, tab)
Pl20 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ inc \geq 1 /\ Enum(n, tab_out) = Enum(n, tab)
Pl21 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
    /\ inc = 1 /\ Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2 })
Pl22 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2 })
Pl23 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
    /\ inc = 0 /\ Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2 })
Pl24 ==
    /\ FALSE
Pl25 ==
    /\ FALSE
Pl26 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
    /\ inc = 0 /\ Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2 })
Pl27 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
    /\ inc \geq 0 /\ (inc = 0 => Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2 }))
Pl28 ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2 })

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
    /\ pc = "l20" => Pl20
    /\ pc = "l21" => Pl21
    /\ pc = "l22" => Pl22
    /\ pc = "l23" => Pl23
    /\ pc = "l24" => Pl24
    /\ pc = "l25" => Pl25
    /\ pc = "l26" => Pl26
    /\ pc = "l27" => Pl27
    /\ pc = "l28" => Pl28

Pre ==
    /\ n \in Nat
    /\ 0..n - 1 \subseteq DOMAIN tab
Post ==
    /\ 0..n - 1 \subseteq DOMAIN tab_out /\ Enum(n, tab_out) = Enum(n, tab)
    /\ Forall({ tab_out[k] \leq tab_out[k + 1] : k \in 0..n - 2 })

PartialCorrectness == Pre => (pc = "Done" => Post)
InvOk == Pre => Inv
NoRTE ==
    /\ StayInRange(i)
    /\ StayInRange(j)
    /\ StayInRange(inc)
    /\ StayInRange(tmp)

=============================================================================
\* Modification History
\* Last modified Wed Apr 29 12:08:22 CEST 2020 by thomas
\* Created Tue Apr 28 19:13:19 CEST 2020 by thomas
