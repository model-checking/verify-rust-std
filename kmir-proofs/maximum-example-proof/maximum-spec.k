module MAXIMUM-SPEC
  imports KMIR

 claim [maximum-spec]:
  <k>
    ( // LHS, start state
      #execTerminator ( 
          terminator (... 
              kind: terminatorKindCall (... 
                  func: operandConstant (
                      constOperand (... 
                          span: span ( 50 ) ,
                          userTy: noUserTypeAnnotationIndex ,
                          const: mirConst (... 
                              kind: constantKindZeroSized , 
                              ty: ty ( 25 ) , // <- this is the reference to `maximum`
                              id: mirConstId ( 9 ) 
                          )
                      )
                  ) ,
                  args: 
                      operandCopy ( place (... local: local ( 1 ) , projection: .ProjectionElems ) )
                      operandCopy ( place (... local: local ( 2 ) , projection: .ProjectionElems ) )
                      operandCopy ( place (... local: local ( 3 ) , projection: .ProjectionElems ) ),
                  destination: DEST,
                  target: noBasicBlockIdx,
                    // forcing the proof to stop because there is no caller to return to
                  unwind: _
              ),
              span: _
          )
      ) 
    => 
      // RHS: target
      // #execTerminator ( terminator (... kind: terminatorKindReturn , span: ?_ ) )
      #EndProgram
    )
    ~> .K
  </k>
  <retVal> _ </retVal>
  <currentFunc> _ => ty ( 25 ) </currentFunc>
  <currentFrame>
    <currentBody> _ => ?_ </currentBody>
    <caller> _ => ?_ </caller>
    <dest> _ => DEST </dest>
    <target> _ => noBasicBlockIdx </target>
    <unwind> _ => ?_ </unwind>
    <locals>
      ListItem ( _ )
      ListItem ( typedValue ( Integer ( A , 64 , false ) , ty ( 26 ) , _ ) )
      ListItem ( typedValue ( Integer ( B , 64 , false ) , ty ( 26 ) , _ ) )
      ListItem ( typedValue ( Integer ( C , 64 , false ) , ty ( 26 ) , _ ) )
      // _ // if we keep this we need a lemma for list size predicate simplification
      => 
      ListItem ( typedValue ( Integer ( ?RESULT, 64, false), ty ( 26 ) , ?_ ))
      ?_
    </locals>
  </currentFrame>
  <stack> _ => ?_ </stack>
  <functions>
     ty ( 25 ) |-> monoItemFn (... name: symbol ( "maximum" ) , id: defId ( 7 ) , body: someBody ( body (... blocks: basicBlock (... statements: statement (... kind: statementKindAssign (... place: place (... local: local ( 5 ) , projection: .ProjectionElems ) , rvalue: rvalueBinaryOp ( binOpLt , operandCopy ( place (... local: local ( 1 ) , projection: .ProjectionElems ) ) , operandCopy ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ) ) ) , span: span ( 69 ) )  .Statements , terminator: terminator (... kind: terminatorKindSwitchInt (... discr: operandMove ( place (... local: local ( 5 ) , projection: .ProjectionElems ) ) , targets: switchTargets (... branches: branch ( 0 , basicBlockIdx ( 2 ) )  .Branches , otherwise: basicBlockIdx ( 1 ) ) ) , span: span ( 69 ) ) )  basicBlock (... statements: statement (... kind: statementKindAssign (... place: place (... local: local ( 4 ) , projection: .ProjectionElems ) , rvalue: rvalueUse ( operandCopy ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ) ) ) , span: span ( 71 ) )  .Statements , terminator: terminator (... kind: terminatorKindGoto (... target: basicBlockIdx ( 3 ) ) , span: span ( 70 ) ) )  basicBlock (... statements: statement (... kind: statementKindAssign (... place: place (... local: local ( 4 ) , projection: .ProjectionElems ) , rvalue: rvalueUse ( operandCopy ( place (... local: local ( 1 ) , projection: .ProjectionElems ) ) ) ) , span: span ( 72 ) )  .Statements , terminator: terminator (... kind: terminatorKindGoto (... target: basicBlockIdx ( 3 ) ) , span: span ( 70 ) ) )  basicBlock (... statements: statement (... kind: statementKindAssign (... place: place (... local: local ( 7 ) , projection: .ProjectionElems ) , rvalue: rvalueUse ( operandCopy ( place (... local: local ( 4 ) , projection: .ProjectionElems ) ) ) ) , span: span ( 74 ) )  statement (... kind: statementKindAssign (... place: place (... local: local ( 6 ) , projection: .ProjectionElems ) , rvalue: rvalueBinaryOp ( binOpLt , operandMove ( place (... local: local ( 7 ) , projection: .ProjectionElems ) ) , operandCopy ( place (... local: local ( 3 ) , projection: .ProjectionElems ) ) ) ) , span: span ( 73 ) )  .Statements , terminator: terminator (... kind: terminatorKindSwitchInt (... discr: operandMove ( place (... local: local ( 6 ) , projection: .ProjectionElems ) ) , targets: switchTargets (... branches: branch ( 0 , basicBlockIdx ( 5 ) )  .Branches , otherwise: basicBlockIdx ( 4 ) ) ) , span: span ( 73 ) ) )  basicBlock (... statements: statement (... kind: statementKindAssign (... place: place (... local: local ( 0 ) , projection: .ProjectionElems ) , rvalue: rvalueUse ( operandCopy ( place (... local: local ( 3 ) , projection: .ProjectionElems ) ) ) ) , span: span ( 76 ) )  .Statements , terminator: terminator (... kind: terminatorKindGoto (... target: basicBlockIdx ( 6 ) ) , span: span ( 75 ) ) )  basicBlock (... statements: statement (... kind: statementKindAssign (... place: place (... local: local ( 0 ) , projection: .ProjectionElems ) , rvalue: rvalueUse ( operandCopy ( place (... local: local ( 4 ) , projection: .ProjectionElems ) ) ) ) , span: span ( 77 ) )  .Statements , terminator: terminator (... kind: terminatorKindGoto (... target: basicBlockIdx ( 6 ) ) , span: span ( 75 ) ) )  basicBlock (... statements: .Statements , terminator: terminator (... kind: terminatorKindReturn , span: span ( 78 ) ) )  .BasicBlocks , locals: localDecl (... ty: ty ( 26 ) , span: span ( 79 ) , mut: mutabilityMut )  localDecl (... ty: ty ( 26 ) , span: span ( 80 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 26 ) , span: span ( 81 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 26 ) , span: span ( 82 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 26 ) , span: span ( 83 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 29 ) , span: span ( 69 ) , mut: mutabilityMut )  localDecl (... ty: ty ( 29 ) , span: span ( 73 ) , mut: mutabilityMut )  localDecl (... ty: ty ( 26 ) , span: span ( 74 ) , mut: mutabilityMut )  .LocalDecls , argCount: 3 , varDebugInfo: varDebugInfo (... name: symbol ( "a" ) , sourceInfo: sourceInfo (... span: span ( 80 ) , scope: sourceScope ( 0 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 1 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 1 ) )  varDebugInfo (... name: symbol ( "b" ) , sourceInfo: sourceInfo (... span: span ( 81 ) , scope: sourceScope ( 0 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 2 ) )  varDebugInfo (... name: symbol ( "c" ) , sourceInfo: sourceInfo (... span: span ( 82 ) , scope: sourceScope ( 0 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 3 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 3 ) )  varDebugInfo (... name: symbol ( "max_ab" ) , sourceInfo: sourceInfo (... span: span ( 83 ) , scope: sourceScope ( 1 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 4 ) , projection: .ProjectionElems ) ) , argumentIndex: noInt )  .VarDebugInfos , spreadArg: noLocal , span: span ( 84 ) ) ) )
  </functions>

  requires // invariant of the `Integer` constructor
             0 <=Int A
     andBool A <Int (1 <<Int 64)
     // likewise for B and C, but all are actually irrelevant for the proof here
ensures
            A <=Int ?RESULT 
    andBool B <=Int ?RESULT 
    andBool C <=Int ?RESULT 
    andBool ( A ==Int ?RESULT orBool B ==Int ?RESULT orBool C ==Int ?RESULT)
endmodule
