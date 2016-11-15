module relAcq
open util/relation
open util/ordering[Timestamp] as timestamps

sig Timestamp {}

assert TimestampTotalOrder {
   all disj t0, t1: Timestamp |
      (t0 in timestamps/nexts[t1]) or (t1 in timestamps/nexts[t0])
}
check TimestampTotalOrder for 0 but 10 Timestamp

sig Loc {}
sig Val {}
one sig Zero extends Val {}

sig History {
   t : Loc -> Timestamp -> lone Val
} {}

sig Front {
   t : Loc -> Timestamp
}

sig TId {}

sig State {
   threads : some TId,
   history : History,
   viewfront : threads -> Front
} {}

abstract sig Action {
   pre, post : State
} {}
