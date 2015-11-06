sig RegisteredCostumer {}

sig Zone {
vertices: set Position
} {#vertices = 4}

//position
sig Position{
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
//solver cannot find instances with this right restriction so we commented it

//type of requests
abstract sig Request{
position:Position
}

sig RegisteredRequest extends Request{
costumer:RegisteredCostumer
}

sig GuestRequest extends Request{
phoneNumber: some Int
} {#phoneNumber = 6 and (all x:phoneNumber | x > 0)} //#phoneNumber should be 10 but solver cannot find instances

sig Reservation extends Request{
costumer:RegisteredCostumer,
time:Time
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
		all e:RequestQueueElement | one q:RequestQueue | e in q.root.*next
	}

fact nextNotCyclic { 
	no e:RequestQueueElement | e in e.^next 
}

fact eachRequestInOnlyOneQueue{
	(no disj e1, e2:RequestQueueElement | e1 in RequestQueue.root.*next and e2 in RequestQueue.root.*next and e1.r=e2.r)
}

fact eachRequestInRightZoneQueue{
	(all q:RequestQueue, r1:RequestQueueElement | r1 in q.root.*next implies r1.r.position.zone = q.zone)
}

fact ReservationsHasHigherPriorityThanRequests{
	(all q:RequestQueue, e:RequestQueueElement, r1:Request | (e in q.root.*next and r1 in e.r and not(r1 in Reservation)) implies (no r2:Reservation | r2 in e.next.r))
}

fact aQueuePerZoneAndAZonePerQueue{
	(all z: Zone | one q: RequestQueue | q.zone = z) and (all q: RequestQueue | one z: Zone | q.zone = z)
}

pred enqueueRequest[req: one RequestQueueElement, q, q': one RequestQueue] {
	q.root = q'.root and (not(req.r in Reservation) implies ((one e:RequestQueueElement | e in q'.root.*next and e.next = req) and #req.next=0) else (one e:RequestQueueElement | e in q'.root.*next and e.next = req)  and not (req.next.r in Reservation))
}

pred dequeueTaxi[q, q': one RequestQueue]{
	q'.root = q.root.next
}

pred show{

}

run enqueueRequest for 4 but exactly 2 RequestQueue
