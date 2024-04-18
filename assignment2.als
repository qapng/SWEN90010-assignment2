sig Principal {}

sig Data {}

sig Message {
	seq_num : one Int ,
	src : one Principal ,
	dest : one Principal ,
	data : one Data
}

abstract sig ChannelState {}
one sig Insecure , Secure extends ChannelState {}

abstract sig DebugAction {}
one sig SendAction , RecvAction , AttackerAction , GoSecureAction
	extends DebugAction {}

one sig State {
	// send_counter [ from ][ to] records the number of messages that Principal
	// ’from ’ has sent to Principal ’to ’
	var send_counter : Principal -> Principal -> one Int ,
	// recv_counter [to ][ from ] records the number of messages that Principal
	// ’to ’ has received from principal ’from ’
	var recv_counter : Principal -> Principal -> one Int ,
	var channel_state : one ChannelState ,
	// the network can hold at most one message at a time
	var network : lone Message ,
	// for debugging purposes (to aid reading counter - examples , etc .)
	// records the most recent action that has occurred
	var debug_last_action : lone DebugAction
}

// sender ’from ’ sends a message to receiver ’to ’ with sequence number
// ’seqnum ’ and data ’d’
pred Send [from , to : Principal , seqnum : Int , d : Data ] {
	no State . network
	( some m : Message |
	 m.src = from 
	and m. dest = to 
	and m. seq_num = seqnum
	and seqnum = State . send_counter [from ,to] 
	and m. data = d
	and m in State . network ’)
	State . send_counter ’ = State . send_counter ++ ( from -> to -> (add[seqnum ,1]))
	State . recv_counter ’ = State . recv_counter
	State . channel_state ’ = State . channel_state
	State . debug_last_action ’ = SendAction
}

// receiver ’to ’ receives a message from sender ’from ’ with sequence number
// ’seqnum ’ and data ’d’
pred Recv [from , to : Principal , seqnum : Int , d : Data ] {
	one State.network and no State.network’
	(some m:Message | 
	m.src = from 
	and m.dest = to 
	and m.seq_num = seqnum
	and seqnum = State.recv_counter[to, from] 
	and m.data = d 
	and m not in State.network’
	and m in State.network)
	State.recv_counter’ = State.recv_counter ++ (to -> from -> (add[seqnum, 1]))
	State.send_counter’ = State.send_counter
	State.channel_state’ = State.channel_state
	State.debug_last_action’ = RecvAction
}

// models the establishment of a secure channel
pred Go_Secure {
	no State . network

	//Comment out the 5 lines below for Task 1.1, 1.2, 1.3, 1.4. Uncomment otherwise
	// ( 
	// 	all a,b: Principal |
	// 	State.send_counter’ [ a, b ] = 0
	// 	and State.recv_counter’ [ b, a ] = 0
	// )

	State . channel_state = Insecure and State . channel_state ’ = Secure
	// Comment out 2 lines below for Task 2.1, 2.2, 2.3. Uncomment otherwise
	State . send_counter ’ = State . send_counter
	State . recv_counter ’ = State . recv_counter
	State . network ’ = State . network
	State . debug_last_action ’ = GoSecureAction
}

pred Attacker_Action {
	// send message or modify message
	// Inject: no message in network and channel insecure
	// Remove: message in network
	// Modify: one message in network and channel insecure
	// FILL IN STUFF HERE to define how the attacker can affect State . network ’
	Attacker_Modify 
	or Attacker_Remove 
	or Attacker_Inject
	State . send_counter ’ = State . send_counter
	State . recv_counter ’ = State . recv_counter
	State . channel_state ’ = State . channel_state
	State . debug_last_action ’ = AttackerAction
}

// Similar to Send but no modify counter
pred Attacker_Inject{
	no State . network and one State . network’
	and State . channel_state = Insecure
 
}

// Similar to Recv but no modify counter
pred Attacker_Remove{
	one State.network and no State.network ’
}

// Modify message = remove message and inject new message but no modify counter
pred Attacker_Modify{
	one State.network and one State.network’ 
	and State . channel_state = Insecure
	( some m1,m2 : Message |
	m1 != m2
	and m1 not in State . network ’
	and m2 in State . network ’’)
}

// the initial state
pred Init {
	State . send_counter = Principal -> Principal -> 0
	State . recv_counter = Principal -> Principal -> 0
	State . channel_state = Insecure
	no State . network
	no State . debug_last_action
}

pred State_Transition {
	( some from , to : Principal , seqnum : Int , d : Data |
	Send [from ,to , seqnum ,d] or Recv [from ,to , seqnum ,d])
	or
	Go_Secure
	or
	Do_Nothing
	or
	Attacker_Action
}

pred Do_Nothing {
	State . send_counter ’ = State . send_counter
	State . recv_counter ’ = State . recv_counter
	State . network ’ = State . network
	State . channel_state ’ = State . channel_state
	no State . debug_last_action ’
}
// constrain traces
fact traces {
	Init and
	( always State_Transition )
}

// Task 1.2 assertion in_sync_always
assert in_sync_always{
	always all from:Principal, to:Principal | 
	State.send_counter[from,to] = State.recv_counter [to ,from]
}
//in_sync_always will not hold in general
//assume 2 principals A and B, principal A will be the first to send messages over the channel.
//the sending order is A-B-A-B-A-B-...
//After B sends a message to A and A receives, the counter will now be synced.
//If A then sends a message to B and B receives, only the send_counter for A and recv_counter for B will be incremented
//A's send_counter will be 1 more than B's, and B's recv_counter will be 1 more than A's

// Task 1.3 assertion in_sync NOT SURE
assert in_sync{
	always all from, to:Principal, seqnum : Int , d : Data |
	// no State.network implies State.send_counter[from,to] = State.recv_counter [to ,from]
	Recv[from,to,seqnum,d] implies after (State.send_counter[from,to] = State.recv_counter [to ,from])
}


// Task 1.4
assert security_goal {
		always all a: Principal, b: Principal, seqnum1,seqnum2: Int, d: Data |

		(
			Recv[a, b, seqnum2, d] 
			and State.channel_state = Secure 
		) 
		implies
		(
			(once (Send[a, b, seqnum2, d] and State.channel_state = Secure)) implies
			(once (Send[a, b, seqnum1, d] and State.channel_state = Secure)) implies
			(once (Recv[a, b, seqnum1, d] and State.channel_state = Secure))
		) 
}



assert test {
	always all from, to:Principal, seqnum : Int , d : Data |
	(Recv[from,to,seqnum,d] and seqnum = 1 and State.channel_state = Secure) implies 
	(
		once
		(
			Recv[from,to,0,d] and State.channel_state = Secure
		)
	)
}
check security_goal for 2 but 5..10 steps
check test for 2

check in_sync_always for 2 

// TODO explain when the assertion is violated when attacker attacks 
check in_sync for 2 but 1 State
//assuming there are no attackers in the system, and there are 2 principals A and B
//in_sync checks if the send_counter of A is the same as the recv_counter of B
//and vice versa, after each message is received
//it will hold since the number of messages sent is always equal to the number of messages received
//given the assumption above that there's no interference with the sending/receiving process in the network

pred sendRecv[] {
    some a: Principal, b: Principal, seqnum,seqnum2: Int, d: Data | 
	{
		// Attacker_Action;
        Send[a, b, seqnum, d];
        Recv[a, b, seqnum, d];
		Send[a, b, seqnum2, d];
        Recv[a, b, seqnum2, d]
    }
}

pred attackTestInject[] {
    some a: Principal, b: Principal, seqnum: Int, d: Data | 
	{
        Attacker_Action;
		Recv[a, b, seqnum, d]
    }
}

pred attackTestModify[] {
    some a: Principal, b: Principal, seqnum: Int, d: Data | 
	{
        Send[a, b, seqnum, d];
        Attacker_Action
    }
}

pred attackTestRemove[] {
    some a: Principal, b: Principal, seqnum: Int, d: Data | 
	{
        Go_Secure;
		Send[a, b, seqnum, d];
        Attacker_Action
    }
}

pred pretruncAttack[]{
	some a: Principal, b: Principal, seqnum1,seqnum2,seqnum3: Int, d: Data | 
	{
		Attacker_Action;
		Recv[a, b, seqnum1, d];
		Go_Secure;
		Send[a, b, seqnum2, d];
		Attacker_Action;
		Send[a, b, seqnum3, d];
		Recv[a, b, seqnum3, d]
    }
}

pred goSecure[]{
	some a: Principal, b: Principal, seqnum1: Int, d: Data | 
	{
		Send[a, b, seqnum1, d];
		Recv[a, b, seqnum1, d];
		Go_Secure
    }
}


run goSecure for 2
run sendRecv for 2 
run attackTestInject for 2 
run attackTestModify for 2 
run attackTestRemove for 2 
run pretruncAttack for 2 but 3 Message

//Task 2.1
//We reset the sequence number at the beginning of the Go_Secure predicate.
//We set the send_counter and recv_counter, for the next state, for all principals to 0,
//while commenting out the 2 lines that say "State.send_counter’ = State.send_counter and State.recv_counter = State.recv_counter' "
//This is to ensure the sequence number is not set to the wrong value after we reset it

//Task 2.3

//One obvious vulnerability is that attackers can attack the handshake protocol, whether with modification, injection or removal of messages.
//Because the handshake is formed on the basis of a fixed list of handshake messages instead of the whole transcript when setting up the handshake,
//attackers can manipulate the messages in different ways and cause the handshake to fail.
//The principals will then not be able to establish a secure communication channel.

//Second vulnerability is that if principal A keeps sending messages out but is interrupted and removed by the attackers, 
//the system will not be able to detect that, as the messages will be sent and received in order, which doesn't violate our security goal
//To be specific, due to the simplification of the ststem, the goal states that in order to receive a message, all messages must have been sent and the receiving principal must have received any previous messages in that order.
//However, it means a principal can keep sending messages without the other principal having to receive them.

