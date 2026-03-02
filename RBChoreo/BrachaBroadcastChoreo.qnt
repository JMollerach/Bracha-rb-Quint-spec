/*
 * Quint Specification for Byzantine Reliable Broadcast protocol by Bracha [1], leveraging the Quint choreo library [2].
 * This is a slightly optimized version of the one described in the original paper,
 * preserving the same terminology used by its author.
 *
 * [1] https://ecommons.cornell.edu/server/api/core/bitstreams/62b32313-c452-43f5-901a-87000e47ef4d/content
 * [2] https://quint-lang.org/choreo
*/

module BrachaBroadcastChoreo { 
  import basicSpells.* from "spells/basicSpells"
  import choreo(processes = NODES) as choreo from "choreo"
  
  const N: int //Number of nodes
  const T: int //Number of byzantine nodes
  const V: int //Number of possible values

  // =============================================================================
  // MANDATORY TYPE DEFINITIONS
  // =============================================================================

  type Node = int

  type Role = Transmitter | Participant

  type Message = {source: int, messageType: str, value: int}

  type StateFields = {
    role: Role,
    value: int,
    is_honest: bool,
    echoed: bool,
    accepted: Option[int],
  }

  type CustomEffects = ()
  type Event = ()
  type Extensions = ()

  // =============================================================================
  // BOILERPLATE (no need to modify - unless you rename something)
  // =============================================================================
  type LocalState = choreo::LocalState[Node, StateFields]
  type LocalContext = choreo::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition = choreo::Transition[Node, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[
    Node,
    StateFields,
    Message,
    Event,
    Extensions
  ]

  // =============================================================================
  // HELPER FUNCTIONS
  // =============================================================================

  // =============================================================================
  // TRANSITION FUNCTIONS
  // =============================================================================

  pure def step0(ctx:LocalContext): Set[Transition] = {
    if (ctx.state.role == Transmitter 
        and (ctx.state.is_honest implies not(ctx.messages.exists(m => m.messageType == "INITIAL")))
        ) {
          Set({
            effects: Set(
              choreo::Broadcast({messageType:"INITIAL",value: ctx.state.value, source: ctx.state.process_id})
              ),
            post_state: {...ctx.state}
          })
        } else {
          Set()
        }
  }

  pure def byzstep0(ctx:LocalContext): Set[Transition] = {
    if (ctx.state.role == Transmitter 
    and not(ctx.state.is_honest)) {
        1.to(V).map(value => {
          effects: Set(
              choreo::Broadcast({messageType:"INITIAL",value: value, source: ctx.state.process_id})
              ),
          post_state: {...ctx.state}
        })
    } else {
      Set()
    }
  }

  pure def listen_for_initial(ctx: LocalContext): Set[int] = {
    if (ctx.state.echoed == false) {
      ctx.messages.filter(m => m.messageType == "INITIAL").map(m => m.value)
    } else {
      Set()
    }
  }

  pure def handle_initial(ctx: LocalContext, value: int): Transition = {
    {
      effects: Set(
        choreo::Broadcast({messageType:"ECHO",value: value, source: ctx.state.process_id})
      ),
      post_state: {
        ...ctx.state,
        echoed: true
      }
    }
  }

  pure def listen_for_amplification(ctx: LocalContext): Set[int] = {
    val received_values = ctx.messages.map(m => m.value)

    received_values.filter(v => 
      ctx.messages.filter(m => m.messageType == "ECHO" and m.value == v).size() >= 2 * T + 1 
      or 
      ctx.messages.filter(m => m.messageType == "READY" and m.value == v).size() >= T + 1
    )
  }

  pure def handle_amplification(ctx:LocalContext, value: int): Transition = {
    {
      effects: Set(
        choreo::Broadcast({messageType:"READY",value: value,source: ctx.state.process_id})
      ),
      post_state: {...ctx.state}
    }
  }

  pure def listen_for_ready(ctx:LocalContext): Set[int] = {
    val received_values = ctx.messages.map(m => m.value)
    
    received_values.filter(v => ctx.messages.filter(m => m.messageType == "READY" and m.value == v).size() >= 2*T+1)
  }

  pure def handle_ready(ctx:LocalContext, value: int): Transition = {
    {
      effects: Set(
        choreo::Broadcast({messageType:"READY",value: value, source: ctx.state.process_id})
      ),
      post_state: {...ctx.state, accepted: Some(value)}
    }
  }

  // =============================================================================
  // MAIN LISTENER
  // =============================================================================

  pure def main_listener(ctx: LocalContext): Set[Transition] = {
    Set(
      choreo::cue(ctx,listen_for_initial,handle_initial),
      choreo::cue(ctx,listen_for_amplification,handle_amplification),
      choreo::cue(ctx,listen_for_ready,handle_ready),
      step0(ctx),
      byzstep0(ctx)
    ).flatten()
  }

  // =============================================================================
  // PROTOCOL CONFIGURATION
  // =============================================================================

  pure val NODES: Set[int] = 1.to(N)

  // =============================================================================
  // INITIALIZATION
  // =============================================================================

  // Initialize each process's local state
  def initialize(n: Node, transmitter: Node, v:int): LocalState =
      {
        process_id: n,
        role: if (n == transmitter) Transmitter else Participant,
        value: v,
        is_honest: n > T,
        echoed: false,
        accepted: None,
      }

  // Initial global state
  action init = 
    nondet transmitter = NODES.oneOf()
    nondet initial_values = NODES.setOfMaps(1.to(V)).oneOf()
    choreo::init(
    {
      system: NODES.mapBy(n => initialize(n,transmitter,initial_values.get(n))),
      messages: NODES.mapBy(n => Set()),
      events: NODES.mapBy(n => Set()),
      extensions: () 
    })

  // =============================================================================
  // STEP FUNCTION
  // =============================================================================

  action step = choreo::step(
    main_listener,
    (c, _) => c
  )

  val s = choreo::s
  pure def convert_context(env,p) = choreo::convert_context(env,p)
}

//REPL:quint -r RBChoreo/BrachaBroadcastChoreo.qnt::bracha4Nodes1Byzantine2Values
//Random Run: quint run --main bracha4Nodes1Byzantine2Values RBChoreoBrachaBroadcastChoreo.qnt
module bracha4Nodes1Byzantine2Values {
    import BrachaBroadcastChoreo(N=4,V=2,T=1).*
}