//UTILITIES
open util/boolean
sig Float {}

// SIGNATURES

//Type of users
abstract sig User{
}

abstract sig RegisteredUser{
firstName: String,
lastName: String,
email: String,
username: String,
password: String
}

sig RegisteredCostumer extends RegisteredUser{}

sig TaxiDriver extends RegisteredUser {
position: Position,
available: Bool
}

sig GuestUser extends User{}

//zone
sig Zone {
vertices: set Position
} {#vertices = 4}

//position
sig Position{
longitude: Float,
latitude: Float,
zone: Zone
}

//time
sig Time{/*
year:Int,
month: Int,
day: Int,
hours: Int,
mins: Int*/
} 
//{year>0 and month>0 and month<=12 and day>0 and day<=31 and hours>=0 and hours<=23 and mins>0 and mins<60}

//type of requests
abstract sig Request{
position:Position
}

sig RegisteredRequest{
costumer:RegisteredCostumer
}

sig GuestRequest{
phoneNumber: some Int
} {#phoneNumber = 6 and (all x:phoneNumber | x > 0)} //#phoneNumber should be 10 but solver cannot find instances

sig Reservation{
costumer:RegisteredCostumer,
time:Time
}

//queue signatures
sig TaxiQueueElement {
t: TaxiDriver,
next: lone TaxiQueueElement
}

sig TaxiQueue{
zone: Zone,
root: TaxiQueueElement
}

sig RequestQueueElement {
r: Request,
next: lone RequestQueueElement
}

sig RequestQueue{
zone: Zone,
root: RequestQueueElement
}

//FACTS
fact allElementsBelongToSomeQueue {
		all e:TaxiQueueElement | one q:TaxiQueue | e in q.root.*next and
		all e:RequestQueueElement | one q:RequestQueue | e in q.root.*next
	}

fact nextNotCyclic { 
	no e:TaxiQueueElement | e in e.^next
	no e:RequestQueueElement | e in e.^next 
}
/*
fact eachTaxiInOnlyOneQueue{
	(no disj e1, e2:TaxiQueueElement | e1 in TaxiQueue.root.*next and e2 in TaxiQueue.root.*next and e1.t=e2.t)
}
*/
fact eachRequestInOnlyOneQueue{
	(no disj e1, e2:RequestQueueElement | e1 in RequestQueue.root.*next and e2 in RequestQueue.root.*next and e1.r=e2.r)
}

fact eachRequestInRightZoneQueue{
	(all q:RequestQueue, r1:RequestQueueElement | r1 in q.root.*next implies r1.r.position.zone = q.zone)
}

fact ifTaxiInQueueThenAvailable {no t1:TaxiDriver | t1 in TaxiQueueElement.t and t1.available = False}

fact ifTaxiNotInQueueThenUnavailable  {no t1:TaxiDriver | not(t1 in TaxiQueueElement.t) and t1.available = True}

fact aQueuePerZoneAndAZonePerQueue{
	(all z: Zone | one q: TaxiQueue | q.zone = z) and (all q: TaxiQueue | one z: Zone | q.zone = z) and
	(all z: Zone | one q: RequestQueue | q.zone = z) and (all q: RequestQueue | one z: Zone | q.zone = z)
}

fact noMultipleRegistrationForSameEmail { no disj ru1, ru2:RegisteredUser | (ru1.email = ru2.email)}

fact univoqueUsername { no disj ru1, ru2:RegisteredUser | (ru1.username = ru2.username)}

//PREDICATES

pred enqueTaxi[t:TaxiQueueElement, q, q':TaxiQueue] {

}

pred enqueRequest() {}

pred show(){
#TaxiQueue>0
all q:TaxiQueue | #(q.root.*(this/TaxiQueueElement <: next))>1
#GuestRequest>0
}

run enqueTaxi for 10 but exactly 10 String, exactly 2 TaxiQueue
