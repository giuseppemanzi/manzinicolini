open util/boolean

abstract sig User{
}

abstract sig RegisteredUser{/*
firstName: String,
lastName: String,
email: String,
username: String,
password: String*/
}

sig Position{
}

sig TaxiDriver extends RegisteredUser {
position: Position,
available: Bool
}

sig TaxiQueueElement {
t: TaxiDriver,
next: lone TaxiQueueElement
}

sig TaxiQueue{
root: TaxiQueueElement
}

fact allElementsBelongToSomeQueue {
		all e:TaxiQueueElement | some q:TaxiQueue | e in q.root.*next
	}

fact nextNotCyclic { 
	no e:TaxiQueueElement | e in e.^next
}

fact eachTaxiInOnlyOneQueue{
	(no disj e1, e2:TaxiQueueElement | e1 in TaxiQueue.root.*next and e2 in TaxiQueue.root.*next and e1.t=e2.t)
}


fact ifTaxiInQueueThenAvailable {no t1:TaxiDriver | t1 in TaxiQueueElement.t and t1.available = False}

fact ifTaxiNotInQueueThenUnavailable  {no t1:TaxiDriver | not(t1 in TaxiQueueElement.t) and t1.available = True}

//fact noMultipleRegistrationForSameEmail { no disj ru1, ru2:RegisteredUser | (ru1.email = ru2.email)}

//fact univoqueUsername { no disj ru1, ru2:RegisteredUser | (ru1.username = ru2.username)}

pred show {
#TaxiQueue>0
all q:TaxiQueue | #(q.root.*(this/TaxiQueueElement <: next))>1
}

pred enqueueTaxi[t: one TaxiQueueElement, q, q': one TaxiQueue] {
	q.root = q'.root and (one e:TaxiQueueElement | e in q'.root.*next and e.next = t) and #t.next=0
}

pred dequeueTaxi[q, q': one TaxiQueue] {
	q'.root = q.root.next
}

run enqueueTaxi  for 10 but exactly 1 TaxiQueue
