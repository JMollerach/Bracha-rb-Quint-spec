module ReliableBroadcast {
    const N: int
    const V: int
    const T: int

    type Message = { source: int, messageType: str, value: int}
    type Option[a] = Some(a) | None

    var messages: Set[Message]
    var transmitter: int
    var accepted: int -> Option[int]
    var echoed: int -> bool

    val procs: Set[int] = 1.to(N - 1)

    action init = all {
        nondet leader = oneOf(procs)
        transmitter' = leader,
        messages' = Set(),
        accepted' = procs.mapBy(x => None),
        echoed' = procs.mapBy(x => false)
    }

    action send(m) = all {
        messages' = messages.union(Set(m)),
    }

    action step0(p,v) = all {
        p == transmitter,
        send({source: p, messageType:"INITIAL",value: v}),
        transmitter' = transmitter,
        accepted' = accepted,
        echoed' = echoed 
    }

    action step1(p,v) = all {
        echoed.get(p) == false,
        or {
            messages.contains({source:transmitter,messageType:"INITIAL",value: v}),
            size(messages.filter(x => x.messageType == "ECHO" and x.value == v)) >= ((N+T)/2),
            size(messages.filter(x => x.messageType == "READY" and x.value == v)) >= (T+1)
        },
        send({source:p, messageType: "ECHO",value:v}),
        transmitter'=transmitter,
        accepted' = accepted,
        echoed' = echoed.set(p,true),
    }

    action step2(p,v) = all {
        or {
            size(messages.filter(x => x.messageType == "ECHO" and x.value == v)) >= ((N+T)/2),
            size(messages.filter(x => x.messageType == "READY" and x.value == v)) >= (T+1)
        },
        send({source:p, messageType: "READY",value:v}),
        transmitter'=transmitter,
        accepted' = accepted,
        echoed' = echoed
    }

    action step3(p,v) = all {
        size(messages.filter(x => x.messageType == "READY" and x.value == v)) >= (2*T + 1),
        accepted' = accepted.set(p,Some(v)),
        transmitter' = transmitter,
        messages' = messages,
        echoed' = echoed
    }

    action step = {
        nondet v = 1.to(V).oneOf()
        nondet p = procs.oneOf()
        any {
            step0(p,v),
            step1(p,v),
            step2(p,v),
            step3(p,v),
        }
    }
}

module bracha532 {
    import ReliableBroadcast(N=5,V=3,T=2).*
}