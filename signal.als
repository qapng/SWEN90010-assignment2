
// Names of you and your partner:
// Xiaotian Li 1141181
// Junrong Wu 1310531

// the type of addresses
abstract sig Address {}

// some addresses are controlled by potential attackers
sig AttackerAddress extends Address {}

// one address belongs to the User who we model in this file
one sig UserAddress extends Address {}

// the four message types used in the protocol
abstract sig MessageType {}
one sig SDPOffer, SDPAnswer, SDPCandidates, Connect 
  extends MessageType {}

// a message has a type, plus a source (sender) and
// destination (receiver) addresses
sig Message {
  type  : MessageType,
  source: Address,
  dest  : Address,
}


// the seven recorded call states
// SignallingOffered, SignallingOngoing are used only by the caller
// SignallingStart, SignallingAnswered, and Answered are used by the 
// callee
// SignallingComplete is used by both caller and callee
abstract sig CallState {}
one sig SignallingStart, SignallingOffered, SignallingAnswered,
        SignallingOngoing,
        SignallingComplete, Answered, Connected 
  extends CallState {}


/* caller                                 callee
   ------                                 ------
                   ---- SDPOffer --->  
   SignallingOffered                          
                                          SignallingStart
                    <--- SDPAnswer ----
                                          SignallingAnswered
   SignallingOngoing
                  ---- SDPCandidates --->
   SignallingComplete
                                          SignallingComplete
                                                              ------ ringing >> 
                                                              <<--- user answers
                                          Answered
                  <---- Connect -------
                                          audio connected
   audio connected
                                          
*/
   
// the state of the system
one sig State {
  var ringing: lone Address, // whether the User is ringing and if so for whicih caller
  var calls: Address -> lone CallState, // the recorded call state for each call currently in progress
  var audio: lone Address,  // the participant that the User's audio is connected to
  var last_answered: lone Address, // the last caller the User answered a call from
  var last_called: lone Address,   // the last callee that the User called
  var network: lone Message        // the network, records the most recent message sent 
}


// precondition for the User to send a message m in state s
pred user_send_pre[m : Message] {
  m.source in UserAddress and
  (
   (m.type in SDPOffer and m.dest = State.last_called and no State.calls[m.dest]) or
   (m.type in SDPAnswer and State.calls[m.dest] = SignallingStart) or
   (m.type in SDPCandidates and State.calls[m.dest] = SignallingOngoing) or
   (m.type in Connect and State.calls[m.dest] = Answered and
     State.last_answered = m.dest)
  )
}

// precondition for the User to receive a message m in state s
pred user_recv_pre[m : Message] {
  m in State.network and
  m.dest in UserAddress and
  (
   (m.type in SDPOffer and no State.calls[m.source]) or
   (m.type in SDPAnswer and State.calls[m.source] = SignallingOffered) or
   (m.type in SDPCandidates and State.calls[m.source] = SignallingAnswered) or
   (m.type in Connect 
    and State.calls[m.source] = SignallingComplete

   /* FIX: Before receive message, 
    * check whether the source is match the record 
    */
    // and State.last_called = m.source
   )
  )
}

// postcondition for the user sending a message m.
// s is the state the message is sent in and s' is the state
// after sending the message
//
// No need to specify here that last_called and last_answered to not change
pred user_send_post[m : Message] {
  // sending a message adds it to the network
  State.network' = m and
  // FILL IN HERE
  (
    (m.type in SDPOffer and 
    State.calls' = State.calls + (m.dest -> SignallingOffered) and
    // other parts of the system is unchanged
    State.ringing' = State.ringing and
    State.audio' = State.audio) or

   (m.type in SDPAnswer and 
    State.calls' = State.calls ++ (m.dest -> SignallingAnswered) and
    // other parts of the system is unchanged
    State.ringing' = State.ringing and
    State.audio' = State.audio) or   

   (m.type in SDPCandidates and 
    State.calls' = State.calls ++ (m.dest -> SignallingComplete) and
    // other parts of the system is unchanged
    State.ringing' = State.ringing and
    State.audio' = State.audio) or  

   (m.type in Connect and 
    // Ignore Connected according to announcement
    // State.calls' = State.calls ++ (m.dest -> Connected) and
    State.calls' = State.calls and
    /* Sending the Connect message causes 
     * the audio to be connected to the message’s destination
     */
    State.audio' = m.dest and
    // other parts of the system is unchanged
    State.ringing' = State.ringing
    )
  )
}

// postcondition for the user receiving a message m
// s is the state before the message was received; s'
// is hte state after the message was received
//
// No need to specify here that last_called and last_answered to not change
pred user_recv_post[m : Message] {
  // receiving a message removes it from the network
  no State.network' and
  // FILL IN HERE
  (
    (m.type in SDPOffer and
    State.calls' = State.calls + (m.source -> SignallingStart) and
    State.ringing' = State.ringing and
    State.audio' = State.audio) or

   (m.type in SDPAnswer and
    State.calls' = State.calls ++ (m.source -> SignallingOngoing) and
    State.ringing' = State.ringing and
    State.audio' = State.audio) or

   (m.type in SDPCandidates and
    State.calls' = State.calls ++ (m.source -> SignallingComplete) and

    /* Receiving the SDPCandidates message causes the ringing 
    * state to be updated to refer to the message’s source address
    */
    State.ringing' = m.source and
    State.audio' = State.audio) or

   (m.type in Connect and
    // Ignore Connected according to announcement
    // State.calls' = State.calls ++ (m.source -> Connected) and
    State.calls' = State.calls and
    State.ringing' = State.ringing and

    /* receiving the Connect message causes the audio to be 
    * connected to the message’s source address.
    */
    State.audio' = m.source)
  )
}

// the action of the attacker sending a message
// s is the state before the message is sent, s' is the state after
pred attacker_msg {
  some m : Message | m.source in AttackerAddress and
  State.network' = m and
  State.calls' = State.calls and
  State.audio' = State.audio and
  State.ringing' = State.ringing and
  State.last_called' = State.last_called and
  State.last_answered' = State.last_answered
}

// the action of the user either sending or receiving a message
pred user_msg {
  State.last_answered' = State.last_answered and
  State.last_called' = State.last_called and
  some m : Message |
    (user_send_pre[m] and user_send_post[m]) or
    (user_recv_pre[m] and user_recv_post[m])
}

// the action of the user deciding to answer a ringing call
// doing so removes the "ringing" information from the state
// and changes the recorded call state to Answered but otherwise
// does not modify anything
pred user_answers {
  some caller : Address |
  State.calls[caller] in SignallingComplete and
  State.ringing = caller and 
  State.audio' = State.audio and
  no State.ringing' and
  State.calls' = State.calls ++ (caller -> Answered) and
  State.last_answered' = caller and
  State.last_called' = State.last_called and
  State.network' = State.network
}

// teh action of the user deciding to call another participant
// doing so simply updates the last_called state and also cancels
// any current "ringing" state
pred user_calls {
  some callee : Address | State.last_called' = callee and
  State.network' = State.network and
  State.calls' = State.calls and
  State.last_answered' = State.last_answered and
  State.audio' = State.audio and
  no State.ringing'   // calling somebody else stops any current ringing call
}

pred state_unchanged {
  State.network' = State.network
  State.calls' = State.calls
  State.last_answered' = State.last_answered
  State.last_called' = State.last_called
  State.ringing' = State.ringing
  State.audio' = State.audio
}

// a state transition is either the user sending or receiving a msg
// or answering a call, or choosing to call somebody, or the attacker
// sending a message on the network
pred state_transition {
  user_msg or user_answers or
  attacker_msg  or user_calls
  or state_unchanged
}

// defines the initial state
// purposefully allow starting in a state where the User already
// wants to call somebody
pred init {
    no State.audio and no State.ringing and
    no State.last_answered and
    no State.network and
    all dest : Address | no State.calls[dest]
}

fact {
  init
}

fact {
  always state_transition
}

// a  bad state is one in which the User's audio is connected
// to a participant but the User has not yet decided to call that
// participant or to answer a call from them
assert no_bad_states {
 // FILL IN HERE
 // for all states in the system, no bad state will occur
 always not my_bad_state
}

// describe the vulnerability that this check identified
// The markers will reverse the "fix" to your model that you
// implemented and then run this "check" to make sure the vulnerability
// can be seen as described here.
// FILL IN HERE

/* Bad state: the User's audio is connected
 * to a participant but the User has not yet decided to call that
 * participant or to answer a call from them
 */
pred my_bad_state {
  some participant : Address |
    State.audio = participant and 
    no State.last_answered and 
    no State.last_called
}

// Choose a suitable bound for this check to show hwo the
// vulnerability does not arise in your fixed protocol
// Justify / explain your choice of your bound and
// specifically, what guarantees you think are provided by this check.
// FILL IN HERE
// See the assignment handout for more details here.

/** 
 * check 2 instances in defalt, but 4 messages instances, and 8 states
 * The scope bound is tested one by one, and less than 4 messages and
 * 8 states can not generate counter examples
 *
 * From the counter example diagram in Alloy, four messages'
 * Source fields are Attacker Address, and call states are not 
 * ready to connect.
 *
 * For the fix plan, pls see the last lines of comments in this file
 * 
 * If apply FIX codes, the following check will generate no counter examples;
 * If comment out FIX codes, the check will generate counter examples.
 */
check no_bad_states for 2 but 4 Message, 8..8 steps expect 1 

// check the fix for a higher bound 
// (Use it when fix code is applied, should no counter examples)
check no_bad_states for 2 but 8 Message, 4 Address, 12..12 steps

// Alloy "run" commands and predicate definitions to
// showing successful execution of your (fixed) protocol
// FILL IN HERE
// These should include
// (1) The user successfully initiates a call (i.e. is the caller), 
// resulting in their audio being connected to the callee
// (2) The user makes a call and receives a call in the same 
// execution trace, so that in one state their audio is connected 
// to one participant and in another state it is connected to some
// other participant

/* (1) a successful run as caller, audio being connected to callee */
pred one_run {
    // for all users as callee
    all callee : Address |
      (
        // if user is the callee, and he has been connected by a caller
        State.audio = callee
      )
      implies
      (
        /* The calls state must be successful, 
         * like connected or SignallingComplete, 
         * which means successful call.
         */
        // Ignore connected according to announcement
        // State.calls[callee] = Connected
        State.calls[callee] = SignallingComplete
      )
}

/* (2) in one state their audio is connected 
 * to one participant and in another state it is connected to some
 * other participant
 */
pred two_run {
  // for all user pairs
  all one_user, another_user : Address |
    (
      // If two different users, and
      one_user != another_user and
      // in one state, user connect to one user,
      State.audio = one_user 
    )
    implies
    (
      // then, in the another state, to another different user
      State.audio' = another_user
    )
}

/* try run  */
/* run with 6 Message instances, 3 Address and 8 states */
run one_run for 2 but 4 Message, 8..8 steps expect 1

run two_run for 2 but 8 Message, 3 Address, 16..16 steps expect 1


// Describe how you fixed the model to remove the vulnerability
// FILL IN HERE
// Your description should have enough detail to allow somebody
// to "undo" (or "reverse") your fix so we can then see the vulnerability
// in your protocol as you describe it in comments above

/* 
 * Vulnerability Fix:
 * When user is receiving message, system will not check whether the
 * message source matches the last callee that the User called or not.
 * As a result, attckers can freely setup a audio connection with client,
 * no matter what the client state is in.
 * 
 * Fix it by adding a message src check in the user receive pre logic.
 *
 * See: FIX comment in user_recv_pre prediction
 */
