open util/boolean
open util/integer
//
sig Float {} 

//
abstract sig User{
}

abstract sig RegisteredUser{
firstName: String,
lastName: String,
email: String,
username: String,
password: String
}

//
sig RegisteredCostumer extends RegisteredUser{}

sig TaxiDriver extends RegisteredUser {
position: Position,
available: Bool
}

//
sig Zone {
vertices: set Position
} {#vertices = 4}

sig Position{
longitude: Float,
latitude: Float
}

sig TaxiQueueElement {
t: TaxiDriver,
next: lone TaxiQueueElement
}

sig TaxiQueue{
zone: Zone,
root: TaxiQueueElement
} 
//facts
fact allElementsBelongToSomeQueue {
		all e:TaxiQueueElement | one q:TaxiQueue | e in q.root.*next
	}

fact nextNotCyclic { no e:TaxiQueueElement | e in e.^next }

fact {no disj e1, e2:TaxiQueueElement | e1 in TaxiQueue.root.*next and e2 in TaxiQueue.root.*next and e1.t=e2.t}
fact {no t1:TaxiDriver | t1 in TaxiQueueElement.t and t1.available = False}

fact aQueuePerZoneAndAZonePerQueue{(all z: Zone | one q: TaxiQueue | q.zone = z) and (all q: TaxiQueue | one z: Zone | q.zone = z)}

fact noMultipleRegistrationForSamePerson { no disj ru1, ru2:RegisteredUser | (ru1.firstName=ru2.firstName and ru1.lastName=ru2.lastName)}
fact univoqueUsername { no disj ru1, ru2:RegisteredUser | ru1.username = ru2.username}


pred show(){
#TaxiQueue>0
all q:TaxiQueue | #(q.root.*(this/TaxiQueueElement <: next))>1
}

run show for 8 but exactly 10 String
