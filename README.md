## Bracha's reliable broadcast Quint spec

The spec is heavily based in the pseudocode provided in the paper:

### Pseudocode
```
    // leader with input v
   send <v> to all parties

   // Party j (including the leader)
   echo = true
   
   on receiving <v> from leader:
      if echo == true:
         send <echo, v> to all parties
         echo = false

   on receiving <echo, v> from n-f distinct parties:
         send <vote, v> to all parties

   on receiving <vote, v> from f+1 distinct parties:
         send <vote, v> to all parties

   on receiving <vote, v> from n-f distinct parties:
       deliver v
```

Sources:
- [Pseudocode](https://decentralizedthoughts.github.io/2020-09-19-living-with-asynchrony-brachas-reliable-broadcast/)
- [Paper](https://ecommons.cornell.edu/server/api/core/bitstreams/62b32313-c452-43f5-901a-87000e47ef4d/content)