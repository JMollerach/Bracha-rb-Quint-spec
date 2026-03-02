/*
 * Quint Specification for Byzantine Reliable Broadcast protocol by Bracha [1].
 * This is a slightly optimized version of the one described in the original paper,
 * preserving the same terminology used by its author.
 *
 * [1] https://ecommons.cornell.edu/server/api/core/bitstreams/62b32313-c452-43f5-901a-87000e47ef4d/content
*/

module BrachaBroadcast {

    const N: int //Number of nodes
    const T: int //Number of byzantine nodes
    const V: int //Number of possible values

    assume T_RESILIENT = N >= 3*T + 1

    type Message = {source: int, messageType: str, value: int}
    type Option[a] = Some(a) | None

    type GlobalContext = {
        messages: Set[Message],
        transmitter: int,
        echoed: int -> bool,
        accepted: int -> Option[int]
    }

    var context: GlobalContext

    pure val processes: Set[int] = 1.to(N)

    pure def honest(p) = p > T
    pure def faulty(p) = p <= T

    action init = all {
        //assert(N >= 3*T + 1),
        nondet _transmitter = oneOf(processes)
        context' = {
            messages: Set(),
            transmitter: _transmitter,
            accepted: processes.mapBy(x => None),
            echoed: processes.mapBy(x => false)
        }
    }

    action step0(p,v) = all {
        //preconditions
        p == context.transmitter,
        not((context.messages).exists(m => m.messageType == "INITIAL")),

        context' = {...context, messages: context.messages.union(Set({messageType:"INITIAL",value: v, source: p}))},
    }

    action step1(p,v) = all {
        context.echoed.get(p) == false,
        context.messages.contains({messageType:"INITIAL",value: v, source:context.transmitter}),

        context' = {...context, messages: context.messages.union(Set({messageType:"ECHO",value: v, source: p})), echoed: context.echoed.set(p,true)}
    }

    action step2(p,v) = all {
        or {
            2*T+1 <= size(context.messages.filter(x => x.messageType == "ECHO" and x.value == v)),
            T+1 <= size(context.messages.filter(x => x.messageType == "READY" and x.value == v)) //Amplification step
        },

        context' = {...context, messages: context.messages.union(Set({messageType:"READY",value:v, source:p}))},
    }

    action step3(p,v) = all {
        2*T + 1 <= size(context.messages.filter(x => x.messageType == "READY" and x.value == v)),

        context' = {...context, accepted: context.accepted.set(p,Some(v))},
    }

    action step = {
        nondet v = 1.to(V).oneOf()
        nondet p = processes.oneOf()
        any {
            step0(p,v),
            step1(p,v),
            step2(p,v),
            step3(p,v)
        }
    }

    //(Agreement): If two correct processes p and q accept the values v and u respectively then u == v.    
    val agreement = processes.forall(p1 =>
        processes.forall(p2 => or {
            context.accepted.get(p1) == None,
            context.accepted.get(p2) == None,
            (honest(p1) and honest(p2)) implies context.accepted.get(p1) == context.accepted.get(p2)
        }))

    //(validity): If the transmitter is non-faulty then eventually all non-faulty parties will eventually accept the transmitter's input.

    //(totality): If some non-faulty party outputs a value then eventually all non-faulty parties will output a value.
    //write a witness
}


//REPL:quint -r BrachaBroadcast.qnt::bracha4Nodes1Byzantine2Values
//Agreement: quint run --invariant=agreement BrachaBroadcast.qnt --main=bracha4Nodes1Byzantine2Values
//Random Run: quint run --main bracha4Nodes1Byzantine2Values BrachaBroadcast.qnt
module bracha4Nodes1Byzantine2Values {
    import BrachaBroadcast(N=4,V=2,T=1).*
}

//shouldn't work due to T_RESILIENT assumption (it does)
module bracha726 {
    import BrachaBroadcast(N=7,V=2,T=6).*
}

