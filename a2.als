module relAcq
open util/relation
open util/ordering[Timestamp] as timestamps

sig Timestamp {}

assert TimestampIsTotallyOrdered {
   all disj t0, t1: Timestamp |
      (t0 in timestamps/nexts[t1]) or (t1 in timestamps/nexts[t0])
}
check TimestampIsTotallyOrdered for 0 but 10 Timestamp

sig Loc {}
sig Val {}
one sig Zero extends Val {}

sig Front {
   t : Loc -> Timestamp
}

sig History {
   value     : Loc -> Timestamp -> lone Val,
   syncFront : Loc -> Timestamp -> lone Front
} {}

sig TId {}

sig State {
   threads : some TId,
   history : History,
   viewfront : threads -> Front
} {}

abstract sig Action {
   pre, post : State
} {}

abstract sig Modifier {}
one sig Rel, Acq, NA extends Modifier {}

abstract sig Read extends Action {
   loc : Loc,
   val : Val,
   mod : Modifier
}

sig ReadAcq extends Read {} {
   mod = Acq
   pre.threads = post.threads
   pre.history = post.history
}

sig ReadNA extends Read {} {
   mod = NA
}

assert HistoryCorrectDomain {
   all h : History, l : Loc, t : Timestamp |
      (some v : Val   | v = h.value    [l, t]) iff
      (some f : Front | f = h.syncFront[l, t])
}
check HistoryCorrectDomain for 5

/* assert AllReadsAreAcq { */
/*    all t : Read | */
/*       t.mod = Acq or t.mod = NA */
/* } */
/* check AllReadsAreAcq for 2 */
