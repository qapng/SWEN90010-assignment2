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
	no State.network'
	(some m:Message | 
	m.src = from 
	and m.dest = to 
	and m.seq_num = seqnum
	and seqnum = State.recv_counter[to, from] 
	and m.data = d 
	and m not in State.network’)
	State.recv_counter’ = State.recv_counter ++ (to -> from -> (add[seqnum, 1]))
	State.send_counter’ = State.send_counter
	State.channel_state’ = State.channel_state
	State.debug_last_action’ = RecvAction
}

// models the establishment of a secure channel
pred Go_Secure {
	no State . network
	State . channel_state = Insecure and State . channel_state ’ = Secure
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
}

// Similar to Send but no modify counter
pred Attacker_Inject{
	no State . network
	and State . channel_state = Insecure
	( some m : Message |
 	m in State . network ’)
	State . send_counter ’ = State . send_counter
	State . recv_counter ’ = State . recv_counter
	State . channel_state ’ = State . channel_state
	State . debug_last_action ’ = AttackerAction
}

// Similar to Recv but no modify counter
pred Attacker_Remove{
	no State.network ’
	( some m : Message |
	m not in State . network ’)
	State . send_counter ’ = State . send_counter
	State . recv_counter ’ = State . recv_counter
	State . channel_state ’ = State . channel_state
	State . debug_last_action ’ = AttackerAction
}

// Modify message = remove message and inject new message but no modify counter
pred Attacker_Modify{
	one State.network
	and State . channel_state = Insecure
	( some m1,m2 : Message |
	m1 != m2
	and m1 not in State . network ’
	and m2 in State . network ’’)
	State . send_counter ’ = State . send_counter
	State . recv_counter ’ = State . recv_counter
	State . channel_state ’ = State . channel_state
	State . debug_last_action ’ = AttackerAction
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
	all s:State, from:Principal, to:Principal | 
	always (s.send_counter[from,to] = s.recv_counter [to ,from])
}

// Task 1.3 assertion in_sync NOT SURE
assert in_sync{
	all s:State, from:Principal, to:Principal |
	no s.network implies s.send_counter[from,to] = s.recv_counter [to ,from]
}

// Task 1.6
// a sends message1 and message2 (at some time in order maybe not back to back) 
// implies 
// B recieve m2 implies B recieve m1 already
// b recieves m1 implies a send m1 already
// maybe write more than one assertion
assert security_goal{

}

check in_sync_always for 2 but 1 State

// TODO explain when the assertion is violated when attacker attacks 
check in_sync for 2 but 1 State

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

run sendRecv for 2 but 1 State
run attackTestInject for 2 but 1 State
run attackTestModify for 2 but 1 State
run attackTestRemove for 2 but 1 State
