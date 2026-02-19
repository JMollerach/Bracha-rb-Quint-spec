module ReliableBroadcast {
    //Number of nodes
    const N: int
    //Number of faulty nodes
    const T: int
    //Number of possible values
    const V: int

    type Message = { source: int, messageType: str, value: int}
    type Option[a] = Some(a) | None

    //wrap them in a type. "..."
    var messages: Set[Message]
    var transmitter: int
    var echoed: int -> bool
    var accepted: int -> Option[int]

    pure val processes: Set[int] = 1.to(N)

    pure def honest(p) = p > T
    pure def faulty(p) = p <= T

    action init = all {
        nondet leader = oneOf(processes)
        transmitter' = leader,
        messages' = Set(),
        accepted' = processes.mapBy(x => None),
        echoed' = processes.mapBy(x => false)
    }

    action send(m) = all {
        messages' = messages.union(Set(m)),
    }

    action step0(p,v) = all {
        //preconditions
        p == transmitter,
        honest(p) implies not(messages.exists(x => x.messageType == "INITIAL")),

        send({messageType:"INITIAL",value: v, source: p}),

        transmitter' = transmitter,
        accepted' = accepted,
        echoed' = echoed 
    }

    action step1(p,v) = all {
        echoed.get(p) == false,
        or {
            messages.contains({messageType:"INITIAL",value: v, source:transmitter}),

            (N+T)/2 <= size(messages.filter(x => x.messageType == "ECHO" and x.value == v)),

            T + 1 <= size(messages.filter(x => x.messageType == "READY" and x.value == v))
        },

        //to model byzantine behaviour maybe add something like
        //nondet v3 = 1.to(V).oneOf()
        //val v2 = if (honest(p)) v else v3 

        send({messageType: "ECHO",value: v, source: p}),
        echoed' = echoed.set(p,true),
        
        transmitter'=transmitter,
        accepted' = accepted,
    }

    action step2(p,v) = all {
        or {
            size(messages.filter(x => x.messageType == "ECHO" and x.value == v)) >= ((N+T)/2),
            size(messages.filter(x => x.messageType == "READY" and x.value == v)) >= (T+1)
        },

        send({messageType: "READY",value:v, source:p,}),

        transmitter' =transmitter,
        accepted' = accepted,
        echoed' = echoed
    }

    action step3(p,v) = all {
        2*T + 1 <= size(messages.filter(x => x.messageType == "READY" and x.value == v)),

        accepted' = accepted.set(p,Some(v)),

        transmitter' = transmitter,
        messages' = messages,
        echoed' = echoed
    }

    action step = {
        nondet v = 1.to(V).oneOf()
        nondet p = processes.oneOf()
        any {
            step0(p,v),
            step1(p,v),
            step2(p,v),
            step3(p,v),
        }
    }

    //
    val agreement = 1.to(N).forall(x => accepted.get(x) == None or 1.to(N).forall(y => accepted.get(y) == None or accepted.get(x) == accepted.get(y)))
}

//start round and finish rounds
//figure out we are stucked

//multi rounds
//byzantine behaviour


module bracha722 {
    import ReliableBroadcast(N=7,V=2,T=2).*
}