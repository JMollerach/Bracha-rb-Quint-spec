/*
 * Quint Specification for Byzantine Reliable Broadcast protocol by Bracha [1].
 * This is a slightly optimized version of the one described in the original paper,
 * preserving the same terminology used by its author.
 *
 * [1] https://ecommons.cornell.edu/server/api/core/bitstreams/62b32313-c452-43f5-901a-87000e47ef4d/content
*/

module BrachaBroadcast {

    import basicSpells.* from "RBChoreo/spells/basicSpells"

    const N: int //Number of nodes
    const T: int //Number of byzantine nodes
    const V: int //Number of possible values

    assume T_RESILIENT = N >= 3*T + 1

    type Message = {source: int, messageType: str, value: int}
    type Node = int

    type LocalContext = {
        process_id: int,
        echoed: bool,
        accepted: Option[int],
        value: int
    }

    type GlobalContext = {
        messages: Node -> Set[Message],
        transmitter: Node,
        localStates: Node -> LocalContext
    }

    var context: GlobalContext

    pure val processes: Set[int] = 1.to(N)

    pure def honest: Set[int] = T.to(N)
    pure def byzantine: Set[int] = 1.to(T)

    pure def initialize(n: Node, v: int): LocalContext =
      {
        process_id: n,
        value: v,
        echoed: false,
        accepted: None,
      }

    action init: bool = all {
        //assert(N >= 3*T + 1),
        nondet _transmitter = oneOf(processes)
        nondet initial_values = processes.setOfMaps(1.to(V)).oneOf()
        context' = {
            messages: processes.mapBy(n => Set()),
            transmitter: _transmitter,
            localStates: processes.mapBy(n=>initialize(n,initial_values.get(n)))
        }
    }

    pure def step0_post_state(local_context: LocalContext, global_context: GlobalContext, v: int): GlobalContext = {
        {...global_context, 
                    messages: global_context.messages
                                     .transformValues(b => b.setAdd({
                                        source: local_context.process_id, 
                                        messageType: "INITIAL",
                                        value: v
                                        }))
                    }
    }

    pure def step1_post_state(local_context: LocalContext, global_context: GlobalContext, v: int): GlobalContext = {
        {...global_context, 
         messages: global_context.messages
                                 .transformValues(b=>b.setAdd({
                                                    source:local_context.process_id,
                                                    messageType: "ECHO", 
                                                    value: v
                                  })),
         localStates: global_context.localStates
                             .set(local_context.process_id,{...local_context, echoed: true})
                    }
    }

    pure def step2_post_state(local_context: LocalContext, global_context: GlobalContext, v: int): GlobalContext = {
        {...global_context, 
         messages: global_context.messages.transformValues(b=>b.setAdd({
             source: local_context.process_id, 
             messageType: "READY",
             value: v
             }))
         }
    }

    pure def step3_post_state(local_context: LocalContext, global_context: GlobalContext, v: int): GlobalContext = {
        {...global_context,
         localStates: global_context.localStates
                             .set(local_context.process_id,{...local_context,accepted: Some(v)})
         }
    }

    action step0(local_context: LocalContext): bool = all {
        local_context.process_id == context.transmitter,
        step0_post_state(local_context,context,local_context.value) != context, //Avoid stuttering

        context' = step0_post_state(local_context,context,local_context.value)
    }

    action step0byzantine(local_context: LocalContext,v: int): bool = all {
        local_context.process_id == context.transmitter,
        byzantine.contains(local_context.process_id),
        step0_post_state(local_context,context,v) != context, //Avoid stuttering

        context' = step0_post_state(local_context,context,v)
    }

    action step1(local_context: LocalContext,v: int): bool = all {
        local_context.echoed == false,
        context.messages
               .get(local_context.process_id)
               .contains({messageType:"INITIAL",value: v, source:context.transmitter}),
        step1_post_state(local_context,context,v) != context, //Avoid stuttering
        

        context' = step1_post_state(local_context,context,v)
    }

    action step1byzantine(local_context: LocalContext, v: int): bool = all {
        byzantine.contains(local_context.process_id),
        step1_post_state(local_context,context,v) != context, //Avoid stuttering

        context' = step1_post_state(local_context,context,v)
    }

    action step2(local_context: LocalContext, v: int): bool = all {
        or {
            2*T+1 <= context.messages
                            .get(local_context.process_id)
                            .filter(x => x.messageType == "ECHO" and x.value == v)
                            .size(),
            T+1 <= context.messages
                          .get(local_context.process_id)
                          .filter(x => x.messageType == "READY" and x.value == v)
                          .size() //Amplification step
        },
        step2_post_state(local_context,context,v) != context, //Avoid stuttering

        context' = step2_post_state(local_context,context,v)
    }

    action step2byzantine(local_context: LocalContext,v: int): bool = all {
        byzantine.contains(local_context.process_id),
        step2_post_state(local_context,context,v) != context, //Avoid stuttering

        context' = step2_post_state(local_context,context,v)
    }

    action step3(local_context: LocalContext, v: int): bool = all {
        2*T + 1 <= context.messages
                          .get(local_context.process_id)
                          .filter(x => x.messageType == "READY" and x.value == v)
                          .size(),
        step3_post_state(local_context,context,v) != context, //Avoid stuttering
    
        context' = step3_post_state(local_context,context,v)
    }

    action step3byzantine(local_context: LocalContext,v: int): bool = all {
        byzantine.contains(local_context.process_id),
        step3_post_state(local_context,context,v) != context, //Avoid stuttering

        context' = step3_post_state(local_context,context,v)
    }

    action step = {
        nondet v = 1.to(V).oneOf()
        nondet p = processes.oneOf()
        any {
            step0(context.localStates.get(p)),
            step0byzantine(context.localStates.get(p),v),
            step1(context.localStates.get(p),v),
            step1byzantine(context.localStates.get(p),v),
            step2(context.localStates.get(p),v),
            step2byzantine(context.localStates.get(p),v),
            step3(context.localStates.get(p),v),
            step3byzantine(context.localStates.get(p),v)
        }
    }

// Properties
    //(Agreement): If two correct processes p and q accept the values v and u respectively then u == v.    
    
    //(validity): If the transmitter is non-faulty then eventually all non-faulty parties will eventually accept the transmitter's input.

    //(totality): If some non-faulty party outputs a value then eventually all non-faulty parties will output a value.
// Invariants   
    val agreement = processes.exclude(byzantine).forall(p1 =>
        processes.exclude(byzantine).forall(p2 => or {
            context.localStates.get(p1).accepted == None,
            context.localStates.get(p2).accepted == None,
            context.localStates.get(p1).accepted == context.localStates.get(p2).accepted
        }))

// Witnesses
    //quint run BrachaBroadcast.qnt --main bracha4Nodes1Byzantine2Values --witnesses someone_decided
    val someone_decided = processes.exclude(byzantine)
                                   .exists(p1 => context.localStates
                                                        .get(p1).accepted != None)

}

//REPL:quint -r BrachaBroadcast.qnt::bracha4Nodes1Byzantine2Values
//Agreement: quint run --invariant=agreement BrachaBroadcast.qnt --main=bracha4Nodes1Byzantine2Values
//Random Run: quint run --main bracha4Nodes1Byzantine2Values BrachaBroadcast.qnt
module bracha4Nodes1Byzantine2Values {
    import BrachaBroadcast(N=4,V=2,T=1).*
}

