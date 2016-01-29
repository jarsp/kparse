require "domains.k"

module P-SYNTAX
    imports DOMAINS
endmodule

module P-INTERNAL-SYNTAX
    imports DOMAINS
    imports P-SYNTAX
    
    syntax Internal ::= "init"
                      | "initParser"

    syntax Descriptor ::= desc(Int, Int, NonTerminal, Int) // Begin, End, CurrentNT, Alternate
                        | ".Desc"
    syntax CallDescriptor ::= call(Descriptor, Int) // Descriptor, Caller Descriptor
                                                    // For returning, since we can normally
                                                    // match the contexts

    syntax NonTerminal ::= Int

    syntax Ast ::= List
                 | wrap(String, List)

    syntax State ::= EntryState
                   | PrimitiveState
                   | RuleState
                   | ExitState
    
    syntax ProcessDescriptor ::= "nextDescriptor"

    syntax NonTerminalCall ::= nonTerminalCall(Int)
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
endmodule

module P
    imports DOMAINS
    imports P-SYNTAX
    imports P-INTERNAL-SYNTAX

    configuration
    <T>
        <k> initParser ~> init </k>
        <desc> .Desc </desc>
        <queue> .List </queue> 
        <asts> .Map </asts>
        <parser> .Map </parser>
        <program> $PGM:String </program>
        <completed> .Map </completed>
    </T>

    /* Initialization */
    rule <k> initParser => .K ... </k>
         <parser> _ => 0 |-> (0 |-> (entryState ~> primitiveState("a") ~> ruleWrapLabel("#token"))) </parser>

    // Desc |-> 1-level Context |-> Set of possible asts
    rule <k> init => nextDescriptor ... </k>
         <queue> _ => ListItem(call(desc(0, 0, 0, -1), -1)) </queue>
         <asts> Rho => Rho[call(desc(0, 0, 0, -1), -1) <- (.List |-> SetItem(.List))] </asts>

    /* Main Loop */
    rule <k> nextDescriptor => nonTerminalCall(size(As) +Int -1) ... </k>
         <desc> _ => call(desc(B, E, C, -1), P) </desc>
         <queue> ListItem(call(desc(B, E, C, -1), P)) => .List ... </queue>
         <parser> ... C |-> As:Map ... </parser>

    rule <k> nextDescriptor => alternateCall ... </k>
         <desc> _ => desc(B, E, C, A) </desc>
         <queue> ListItem(desc(B, E, C, A)) => .List ... </queue>
         requires A =/=Int -1

    rule <k> nonTerminalCall(S:Int => S +Int -1) ... </k>
         <desc> desc(B, E, C, -1) </desc>
         <queue> ... .List => ListItem(desc(B, E, C, S)) </queue>
         requires S >=Int 0 
    rule <k> nonTerminalCall(-1) => nextDescriptor ... </k>

    // Whenever we have nested maps there appears to be a lengthy process of extraction.
    rule <k> alternateCall => alternateCallProcess(M) ... </k>
         <desc> desc(B, E, C, A) </desc>
         <asts> ... (desc(B, E, C, -1) |-> F) (.Map => desc(B, E, C, A) |-> F) ... </asts>
         <parser> ... C |-> M ... </parser>

    rule <k> alternateCallProcess(M:Map) => M[A] ... </k>
         <desc> desc(_, _, _, A) </desc>

    /* Entry State */
    rule <k> entryState => entryStateProcessContexts(keys(M)) ... </k>
         <desc> D:Descriptor </desc>
         <asts> ... D |-> M ... </asts>

    rule <k> entryStateProcessContexts(Ks:Set SetItem(K))
             => entryStateProcessContexts(Ks) ... </k>
         <desc> D:Descriptor </desc>
         <asts> ... D |-> (M => M[K <- SetItem(.List)]) ... </asts>
    rule entryStateProcessContexts(.Set) => .K

    /* Primitive State */
    // Length 1 tokens atm
    rule <k> primitiveState(T:String) => primitiveStateProcessContexts(T, keys(M), M) ... </k>
         <desc> desc(B, E => E +Int 1, C, A) </desc>
         <asts> ... desc(B, E => E +Int 1, C, A) |-> M ... </asts>
         <program> S:String </program>
         requires T ==String substrString(S, E, E +Int 1)

    rule primitiveStateProcessContexts(T:String, Ks:Set SetItem(K), M:Map)
         => primitiveStateProcessContexts(T, Ks, M) 
            ~> primitiveStateProcessParses(T, K, M[K], .Set)
    rule primitiveStateProcessContexts(_, .Set, _) => .K

    rule primitiveStateProcessParses(T:String, K, As:Set SetItem(A), R:Set)
         => primitiveStateProcessParses(T, K, As, R SetItem(A ListItem(T)))
    rule <k> primitiveStateProcessParses(_, K, .Set, R:Set) => .K ... </k>
         <desc> D:Descriptor </desc>
         <asts> ... D |-> (M => M[K <- R]) ... </asts>

    /* Rules */
    rule <k> ruleWrapLabel(S:String) => ruleWrapLabelProcessContexts(S, keys(M), M) ... </k>
         <desc> D:Descriptor </desc>
         <asts> ... D |-> M ... </asts>
    
    rule ruleWrapLabelProcessContexts(S:String, Ks:Set SetItem(K), M:Map)
         => ruleWrapLabelProcessContexts(S, Ks, M)
            ~> ruleWrapLabelProcessParses(S, K, M[K], .Set)
    rule ruleWrapLabelProcessContexts(_, .Set, _) => .K

    rule ruleWrapLabelProcessParses(S:String, K, As:Set SetItem(A), R:Set)
         => ruleWrapLabelProcessParses(S, K, As, R SetItem(wrap(S, A)))
    rule <k> ruleWrapLabelProcessParses(_, K, .Set, R:Set) => .K ... </k>
         <desc> D:Descriptor </desc>
         <asts> ... D |-> (M => M[K <- R]) ... </asts>

    /* Exit State */
endmodule
