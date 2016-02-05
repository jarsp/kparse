require "domains.k"

module P-SYNTAX
    imports DOMAINS
endmodule

module P-INTERNAL-SYNTAX
    imports DOMAINS
    imports P-SYNTAX
    
    syntax Internal ::= "init"
                      | "initParser"

    syntax Descriptor ::= desc(Int, Int, NonTerminal) // Begin, End, CurrentNT, Alternate
                        | ".Desc"
    syntax CallDescriptor ::= call(Descriptor, NonTerminal) // Descriptor, Caller Descriptor
                                                            // For returning, since we can normally
                                                            // match the contexts
                            | ".Call"

    syntax NonTerminal ::= nt(Int, Int) // Nonterminal, Alternate

    syntax Ast ::= List
                 | wrap(String, List)

    syntax State ::= EntryState
                   | PrimitiveState
                   | RuleState
                   | ExitState
    
    syntax ProcessDescriptor ::= "nextDescriptor"

    syntax NonTerminalCall ::= nonTerminalCall(Int)
                             | "enqueueAlternates"
    syntax AlternateCall ::= "alternateCall"
    syntax AlternateCallProcess ::= alternateCallProcess(Map)

    syntax EntryState ::= "entryState"
    syntax EntryStateProcess ::=  entryStateProcessContexts(Set)
    
    syntax PrimitiveState ::= primitiveState(String)
    syntax PrimitiveStateProcess ::= primitiveStateProcessContexts(String, Set, Map)
                                   | primitiveStateProcessParses(String, K, K, Set)

    syntax RuleState ::= RuleWrapLabel
    syntax RuleWrapLabel ::= ruleWrapLabel(String)
    syntax RuleWrapLabelProcess ::= ruleWrapLabelProcessContexts(String, Set, Map)
                                  | ruleWrapLabelProcessParses(String, K, K, Set)

    syntax ExitState ::= "exitState"
                       | exitStateGetCallers(Set, Set)
                       | exitStateProcessContexts(Set, Map)
                       | exitStateProcessParses(K, K, Set)
endmodule

module P
    imports DOMAINS
    imports P-SYNTAX
    imports P-INTERNAL-SYNTAX

    configuration
    <T>
        <k> initParser ~> init </k>
        <desc> .Call </desc>
        <queue> .List </queue> 
        <asts> .Map </asts>
        <parser> .Map </parser>
        <program> $PGM:String </program>
        <completed> .Map </completed>
    </T>

    /* Initialization */
    // TODO: Work out how to recombine alternates
    rule <k> initParser => .K ... </k>
         <parser> _ => (0 |-> ((-1 |-> (entryState
                                    ~> enqueueAlternates
                                    ~> nextDescriptor
                                    ~> exitState))
                               ( 0 |-> (entryState 
                                    ~> primitiveState("a")
                                    ~> ruleWrapLabel("#token")
                                    ~> exitState))
                              )
                       )
         </parser>

    // Desc |-> 1-level Context |-> Set of possible asts
    rule <k> init => nextDescriptor ... </k>
         <queue> _ => ListItem(call(desc(0, 0, nt(0, -1)), nt(-1, -1))) </queue>
         <asts> Rho => Rho[call(desc(0, 0, nt(0, -1)), nt(-1, -1)) 
                           <- (.List |-> SetItem(.List))] </asts>

    /* Main Loop */
    rule <k> nextDescriptor => nonTerminalCall(size(As) +Int -2) ... </k>
         <desc> _ => call(desc(B, E, nt(C, -1)), NT_P) </desc>
         <queue> ListItem(call(desc(B, E, nt(C, -1)), NT_P)) => .List ... </queue>
         <parser> ... C |-> As:Map ... </parser>

    rule <k> nextDescriptor => alternateCall ... </k>
         <desc> _ => call(desc(B, E, nt(C, A)), NT_P) </desc>
         <queue> ListItem(call(desc(B, E, nt(C, A)), NT_P)) => .List ... </queue>
         requires A =/=Int -1

    // Split into alternates. Pretend the NT call is transparent.
    rule <k> nonTerminalCall(S:Int => S +Int -1) ... </k>
         <desc> call(desc(B, E, nt(C, -1)), NT_P) </desc>
         <queue> ... .List => ListItem(call(desc(B, E, nt(C, S)), NT_P)) </queue>
         requires S >=Int 0 
    rule <k> nonTerminalCall(-1) => nextDescriptor ... </k>

    // Whenever we have nested maps there appears to be a lengthy process of extraction.
    rule <k> alternateCall => alternateCallProcess(M) ... </k>
         <desc> call(desc(B, E, nt(C, A)), NT_P) </desc>
         <asts> ... (call(desc(B, E, nt(C, -1)), NT_P) |-> F) 
                (.Map => call(desc(B, E, nt(C, A)), NT_P) |-> F) ... </asts>
         <parser> ... C |-> M ... </parser>

    rule <k> alternateCallProcess(M:Map) => M[A] ... </k>
         <desc> call(desc(_, _, nt(_, A)), _) </desc>

    /* Entry State */
    rule <k> entryState => entryStateProcessContexts(keys(M)) ... </k>
         <desc> D:CallDescriptor </desc>
         <asts> ... D |-> M ... </asts>

    rule <k> entryStateProcessContexts(Ks:Set (SetItem(K) => .Set)) ... </k>
         <desc> D:CallDescriptor </desc>
         <asts> ... D |-> (M => M[K <- SetItem(.List)]) ... </asts>
    rule entryStateProcessContexts(.Set) => .K

    /* Primitive State */
    // Length 1 tokens atm
    rule <k> primitiveState(T:String) => primitiveStateProcessContexts(T, keys(M), M) ... </k>
         <desc> call(desc(B, E => E +Int 1, nt(C, A)), NT_P) </desc>
         <asts> ... call(desc(B, E => E +Int 1, nt(C, A)), NT_P) |-> M ... </asts>
         <program> S:String </program>
         requires T ==String substrString(S, E, E +Int 1)

    rule primitiveStateProcessContexts(T:String, Ks:Set SetItem(K), M:Map)
         => primitiveStateProcessContexts(T, Ks, M) 
            ~> primitiveStateProcessParses(T, K, M[K], .Set) 
    rule primitiveStateProcessContexts(_, .Set, _) => .K

    rule primitiveStateProcessParses(T:String, K, As:Set (SetItem(A) => .Set), 
                                     R:Set (.Set => SetItem(A ListItem(T))))
    rule <k> primitiveStateProcessParses(_, K, .Set, R:Set) => .K ... </k>
         <desc> D:CallDescriptor </desc>
         <asts> ... D |-> (M => M[K <- R]) ... </asts>

    /* Rules */
    rule <k> ruleWrapLabel(S:String) => ruleWrapLabelProcessContexts(S, keys(M), M) ... </k>
         <desc> D:CallDescriptor </desc>
         <asts> ... D |-> M ... </asts>
    
    rule ruleWrapLabelProcessContexts(S:String, Ks:Set SetItem(K), M:Map)
         => ruleWrapLabelProcessContexts(S, Ks, M)
            ~> ruleWrapLabelProcessParses(S, K, M[K], .Set)
    rule ruleWrapLabelProcessContexts(_, .Set, _) => .K

    rule ruleWrapLabelProcessParses(S:String, K, As:Set (SetItem(A) => .Set), 
                                    R:Set (.Set => SetItem(wrap(S, A))))
    rule <k> ruleWrapLabelProcessParses(_, K, .Set, R:Set) => .K ... </k>
         <desc> D:CallDescriptor </desc>
         <asts> ... D |-> (M => M[K <- R]) ... </asts>

    /* Exit State */
    rule <k> exitState => exitStateGetCallers(keys(Rho), .Set) ... </k>
         <asts> Rho:Map </asts>

    rule <k> exitStateGetCallers(Ks:Set SetItem(call(desc(B_OLD, B, NT_C_OLD), NT_Q)), R:Set)
             => exitStateGetCallers(Ks, R SetItem(call(desc(B_OLD, B, NT_C_OLD), NT_Q))) ... </k>
         <desc> call(desc(B, _, NT_C), _) </desc>
    rule <k> exitStateGetCallers(Ks:Set SetItem(call(desc(_, B_OLD, NT_C_OLD), _)), R:Set)
             => exitStateGetCallers(Ks, R) ... </k>
         <desc> call(desc(B, _, NT_C), _) </desc>
         requires (B_OLD =/=Int B) orBool (NT_C_OLD =/=K NT_C)
    rule exitStateGetCallers(.Set, R:Set) => R

    rule exitStateProcessContexts(Ks:Set SetItem(K), M:Map)
         => exitStateProcessContexts(Ks, M)
            ~> exitStateProcessParses(K, M[K], .Set)
    rule exitStateProcessContexts(.Set, _) => .K
endmodule
