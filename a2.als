module relAcq
open util/relation
open util/ordering[Timestamp] as tsOrder

sig Timestamp {}
one sig ZeroTS extends Timestamp{} {
   tsOrder/first in ZeroTS
}

assert TimestampIsTotallyOrdered {
   all disj t0, t1: Timestamp |
      (t0 in tsOrder/nexts[t1]) or (t1 in tsOrder/nexts[t0])
}
check TimestampIsTotallyOrdered for 0 but 10 Timestamp

sig Loc, Val {}
one sig Zero extends Val {}

sig Front {
   front : Loc -> Timestamp
}

assert frontMergeTest0 {
   all x : Loc | all disj t0, t1 : Timestamp |
      (x -> t0) ++ (x -> t1) = x -> t1
}
check frontMergeTest0 for 2

pred mergeFronts[front0 : Front, front1 : Front, resFront : Front] {
   /* TODO: For some reason 'domain' is a syntactic error.  */
   /* (domain[front1] <: front0) in resFront */
   /* (domain[front0] <: front1) in resFront */
   /* all x : Loc | */
   /*    x in domain[front0] & domain[front1] implies (x -> tsOrder/larger[front0[x], front1[x]]) in resFront */
}

sig HistoryEntry {
   val       : Val,
   syncFront : Front
}

sig TID {}

sig State {
   threads   : set TID,
   viewfront : this.@threads -> Front,
   locations : set Loc,
   history   : this.@locations -> Timestamp -> lone HistoryEntry
}

abstract sig Action {
   tId : TID,
   pre, post : State
} {
   tId in pre.threads
}

pred show {}
run show for 3 but 1 State, 0 Action

abstract sig Modifier {}
one sig Rel, Acq, NA extends Modifier {}

abstract sig Read extends Action {
   loc : Loc,
   val : Val,
   mod : Modifier,
   timestamp : Timestamp
} {
   pre.threads = post.threads
   pre.history = post.history

   val in pre.history[loc, timestamp].val
}

sig ReadAcq extends Read {} {
   mod in Acq

   /* timestamp in pre.viewfront[tId][loc] */

   post.viewfront = pre.viewfront ++ tId -> post.viewfront[tId]
   mergeFronts[post.viewfront[tId], pre.history.syncFront[loc, timestamp], post.viewfront[tId]]
}

sig ReadNA extends Read {} {
   mod in NA
}
