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

//Task 1.1 Recv predicate
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

	// The following block of code models the reset of the sequence number
	// Comment out the 5 lines below for Task 1.1, 1.2, 1.3, 1.4. Uncomment otherwise
	( 
		all a,b: Principal |
		State.send_counter’ [ a, b ] = 0
		and State.recv_counter’ [ b, a ] = 0
	)

	State . channel_state = Insecure and State . channel_state ’ = Secure

	// Comment out 2 lines below for Task 2.1, 2.2, 2.3. Uncomment otherwise
	// State . send_counter ’ = State . send_counter
	// State . recv_counter ’ = State . recv_counter

	State . network ’ = State . network
	State . debug_last_action ’ = GoSecureAction
}

//Task 1.2 Attacker_Action predicate, with helper predicates down below
pred Attacker_Action {
	// Attackers can:
	// Inject: when there is no message in network and the channel is insecure
	// Modify: when there is a message in network and the channel is insecure
	// Remove: when there is a message in network (regardless of channel state)
	Attacker_Modify 
	or Attacker_Remove 
	or Attacker_Inject
	State . send_counter ’ = State . send_counter
	State . recv_counter ’ = State . recv_counter
	State . channel_state ’ = State . channel_state
	State . debug_last_action ’ = AttackerAction
}

// Add a new message to into the network
pred Attacker_Inject{
	no State . network and one State . network’
	and State . channel_state = Insecure
 
}

// Remove a message from the network
pred Attacker_Remove{
	one State.network and no State.network ’
}

// Modify message is equivalent to removing a message and injecting a new one
pred Attacker_Modify{
	one State.network and one State.network’ 
	and State . channel_state = Insecure
	( some m1,m2 : Message |
	m1 != m2
	and m1 not in State . network ’
	and m2 in State . network ’)
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

check in_sync_always for 2 
//Assume 2 principals A and B are in the system, and there are no attackers.
//Aslo assume that the send_counter and recv_counter for both A and B are 0 initially.
//in_sync_always checks if A's send_counter is equal to B's recv_counter, and vice versa, AT ALL TIMES.
//in_sync_always will not hold in general in case that A sends a message, 
//but B hasn't received it yet, and the message is still in the network.
//In that case, since A sent the message, A's send_counter is 1, while B's recv_counter is still 0,
//thus not satisfying the condition that the receiver’s send and receive counters for the sender mirror the sender’s for the receiver.

// Task 1.3 assertion in_sync in suitable conditions
assert in_sync{
	always all from, to:Principal, seqnum : Int , d : Data |
	// no State.network implies State.send_counter[from,to] = State.recv_counter [to ,from]
	Recv[from,to,seqnum,d] implies after (State.send_counter[from,to] = State.recv_counter [to ,from])
}
check in_sync for 2
//Task 1.3 explanation 
//Assuming there are no attackers in the system, and there are 2 principals A and B,
//in_sync checks if the send_counter of A is the same as the recv_counter of B
//and vice versa, after each message is received.
//It will hold since the number of messages sent is always equal to the number of messages received,
//and it only checks the counters once a message, after being sent, is received.
//To be specific, given the assumption above that there's no interference with the sending/receiving processes,
//any message sent will be received successfully.
//The sender's send_counter and receiver's recv_counter will remain equal after that.

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

check security_goal for 2 but 5..15 steps

//The protocol is vulnerable to a prefix truncation attack.
//The protocol has a problem where it does not provide a way to keep track of and compare 
//the send_counter and the recv_counter of both principals. Therefore, if a mismatch in counters happens because
//of an attack, the receiver will not be able to detect it.

//For example, assume A sends out m1, m2 and m3 in that order.
//The attacker can remove m2 from the network, and the receiver will receive m1 and m3 in that order,
//which satisfies the security goal that in order to receive m3, the receiver must have received m1,
//and both m1 and m3 must have been sent.
//The receiver will not, however, know about the existence of m2, even though it was sent earlier by the sender.


//Task 2.1
//We reset the sequence number to 0, when the Go_Secure state transition is executed.
//We set the send_counter and recv_counter, for the next state, for all principals to 0,
//while commenting out the 2 lines that say "State.send_counter’ = State.send_counter and State.recv_counter = State.recv_counter' "
//This is to ensure the sequence number is not set to the wrong value after we reset it

//Task 2.2
//The assertion now holds, as long as the marker comment and uncomment the pieces of code as instructed
//There are two elements to our security goal check, bound and steps.
//For bound, we decide that 2 is enough. The reason being with 2 messages only (A to B, B to A), we are able to detect the vulnerability already.
//If the system are scaled up to multiple principals, it's essentially still pairs of messages being sent and received between any 2 principals,
//and our lower bound is general enough to detect any vulnerabilities.

//For steps, we decide that detecting counter examples ranging from 5 to 15 steps is enough. The reason is that our prefix
//truncation attack is a generalised version in the sense that it performs no redundant operations, and we manage to detect 
//only one counter example that is 8 steps long (when we use 5..10 steps). Therefore, we believe it's highly likely that a larger number of steps
//will not result in a longer counter example. 10 steps is too close to the length of our counter example, so we decided to 
//use 5..15 steps to make sure we don't miss any counter examples. Any more steps than this, it's unlikely to be useful, given
//how long the command will take to run.


//Task 2.3
//One obvious vulnerability is that attackers can attack the handshake protocol, whether with modification, injection or removal of messages.
//Because the handshake is formed on the basis of a fixed list of handshake messages instead of the whole transcript when setting up the handshake,
//attackers can manipulate the messages in different ways and cause the handshake to fail.
//The principals will then not be able to establish a secure communication channel.

//Second vulnerability is that if principal A keeps sending messages out but is interrupted and removed by the attackers, 
//the system will not be able to detect that, as the messages will be sent and received in order, which doesn't violate our security goal
//To be specific, due to the simplification of the ststem, the goal states that in order to receive a message, all messages must have been sent 
//and the receiving principal must have received any previous messages in that order.
//However, it means a principal can keep sending messages without the other principal having to receive them.

//TODO probably add an extension downgrade attack, something to do with problems when all parties go secure