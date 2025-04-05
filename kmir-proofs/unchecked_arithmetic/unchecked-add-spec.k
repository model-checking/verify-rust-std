module UNCHECKED-ADD-SPEC
  imports KMIR

 claim [unchecked-add-spec]:
  <k>
    ( // LHS, start state
      #execTerminator ( 
          terminator (... 
              kind: terminatorKindCall (... 
                  func: operandConstant (
                      constOperand (... 
                          span: span ( 76 ) ,
                          userTy: noUserTypeAnnotationIndex ,
                          const: mirConst (... 
                              kind: constantKindZeroSized , 
                              ty: ty ( 32 ) , // <- this is the reference to `unchecked_op`
                              id: mirConstId ( 12 ) 
                          )
                      )
                  ) ,
                  args: 
                      operandCopy ( place (... local: local ( 1 ) , projection: .ProjectionElems ) )
                      operandCopy ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ),
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
  <currentFunc> _ => ty ( 32 ) </currentFunc>
  <currentFrame>
    <currentBody> _ => ?_ </currentBody>
    <caller> _ => ?_ </caller>
    <dest> _ => DEST </dest>
    <target> _ => noBasicBlockIdx </target>
    <unwind> _ => ?_ </unwind>
    <locals>
      ListItem ( _ )
      ListItem ( typedValue ( Integer ( A , 16 , true ) , ty ( 23 ) , _ ) )
      ListItem ( typedValue ( Integer ( B , 16 , true ) , ty ( 23 ) , _ ) )
      // _ // if we keep this we need a lemma for list size predicate simplification
      => 
      ListItem ( typedValue ( Integer ( ?RESULT, 16, true), ty ( 23 ) , ?_ ))
      ?_
    </locals>
  </currentFrame>
  <stack> _ => ?_ </stack>
  <functions>
    (
      ty ( 32 ) |-> monoItemFn (... name: symbol ( "unchecked_op" ) , id: defId ( 9 ) , body: someBody ( body (... blocks: basicBlock (... statements: .Statements , terminator: terminator (... kind: terminatorKindCall (... func: operandConstant ( constOperand (... span: span ( 93 ) , userTy: noUserTypeAnnotationIndex , const: mirConst (... kind: constantKindZeroSized , ty: ty ( 34 ) , id: mirConstId ( 19 ) ) ) ) , args: operandCopy ( place (... local: local ( 1 ) , projection: .ProjectionElems ) )  operandCopy ( place (... local: local ( 2 ) , projection: .ProjectionElems ) )  .Operands , destination: place (... local: local ( 0 ) , projection: .ProjectionElems ) , target: someBasicBlockIdx ( basicBlockIdx ( 1 ) ) , unwind: unwindActionContinue ) , span: span ( 94 ) ) )  basicBlock (... statements: .Statements , terminator: terminator (... kind: terminatorKindReturn , span: span ( 95 ) ) )  .BasicBlocks , locals: localDecl (... ty: ty ( 23 ) , span: span ( 96 ) , mut: mutabilityMut )  localDecl (... ty: ty ( 23 ) , span: span ( 97 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 23 ) , span: span ( 98 ) , mut: mutabilityNot )  .LocalDecls , argCount: 2 , varDebugInfo: varDebugInfo (... name: symbol ( "a" ) , sourceInfo: sourceInfo (... span: span ( 97 ) , scope: sourceScope ( 0 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 1 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 1 ) )  varDebugInfo (... name: symbol ( "b" ) , sourceInfo: sourceInfo (... span: span ( 98 ) , scope: sourceScope ( 0 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 2 ) )  varDebugInfo (... name: symbol ( "unchecked_sum" ) , sourceInfo: sourceInfo (... span: span ( 99 ) , scope: sourceScope ( 1 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 0 ) , projection: .ProjectionElems ) ) , argumentIndex: noInt )  .VarDebugInfos , spreadArg: noLocal , span: span ( 100 ) ) ) ) 
      ty ( 34 ) |-> monoItemFn (... name: symbol ( "core::num::<impl i16>::unchecked_add" ) , id: defId ( 3 ) , body: someBody ( body (... blocks: basicBlock (... statements: statement (... kind: statementKindStorageLive ( local ( 3 ) ) , span: span ( 43 ) )  statement (... kind: statementKindAssign (... place: place (... local: local ( 3 ) , projection: .ProjectionElems ) , rvalue: rvalueNullaryOp ( nullOpUbChecks , ty ( 21 ) ) ) , span: span ( 44 ) )  .Statements , terminator: terminator (... kind: terminatorKindSwitchInt (... discr: operandMove ( place (... local: local ( 3 ) , projection: .ProjectionElems ) ) , targets: switchTargets (... branches: branch ( 0 , basicBlockIdx ( 2 ) )  .Branches , otherwise: basicBlockIdx ( 1 ) ) ) , span: span ( 43 ) ) )  basicBlock (... statements: .Statements , terminator: terminator (... kind: terminatorKindCall (... func: operandConstant ( constOperand (... span: span ( 45 ) , userTy: noUserTypeAnnotationIndex , const: mirConst (... kind: constantKindZeroSized , ty: ty ( 22 ) , id: mirConstId ( 6 ) ) ) ) , args: operandCopy ( place (... local: local ( 1 ) , projection: .ProjectionElems ) )  operandCopy ( place (... local: local ( 2 ) , projection: .ProjectionElems ) )  .Operands , destination: place (... local: local ( 4 ) , projection: .ProjectionElems ) , target: someBasicBlockIdx ( basicBlockIdx ( 2 ) ) , unwind: unwindActionUnreachable ) , span: span ( 46 ) ) )  basicBlock (... statements: statement (... kind: statementKindStorageDead ( local ( 3 ) ) , span: span ( 48 ) )  statement (... kind: statementKindAssign (... place: place (... local: local ( 0 ) , projection: .ProjectionElems ) , rvalue: rvalueBinaryOp ( binOpAddUnchecked , operandCopy ( place (... local: local ( 1 ) , projection: .ProjectionElems ) ) , operandCopy ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ) ) ) , span: span ( 49 ) )  .Statements , terminator: terminator (... kind: terminatorKindReturn , span: span ( 47 ) ) )  .BasicBlocks , locals: localDecl (... ty: ty ( 23 ) , span: span ( 50 ) , mut: mutabilityMut )  localDecl (... ty: ty ( 23 ) , span: span ( 51 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 23 ) , span: span ( 52 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 21 ) , span: span ( 43 ) , mut: mutabilityMut )  localDecl (... ty: ty ( 1 ) , span: span ( 46 ) , mut: mutabilityNot )  .LocalDecls , argCount: 2 , varDebugInfo: varDebugInfo (... name: symbol ( "self" ) , sourceInfo: sourceInfo (... span: span ( 51 ) , scope: sourceScope ( 0 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 1 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 1 ) )  varDebugInfo (... name: symbol ( "rhs" ) , sourceInfo: sourceInfo (... span: span ( 52 ) , scope: sourceScope ( 0 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 2 ) )  .VarDebugInfos , spreadArg: noLocal , span: span ( 53 ) ) ) )
      ty ( 22 ) |-> monoItemFn (... name: symbol ( "core::num::<impl i16>::unchecked_add::precondition_check" ) , id: defId ( 4 ) , body: someBody ( body (... blocks: basicBlock (... statements: statement (... kind: statementKindStorageLive ( local ( 4 ) ) , span: span ( 55 ) )  statement (... kind: statementKindStorageLive ( local ( 6 ) ) , span: span ( 56 ) )  statement (... kind: statementKindAssign (... place: place (... local: local ( 6 ) , projection: .ProjectionElems ) , rvalue: rvalueCheckedBinaryOp ( binOpAdd , operandCopy ( place (... local: local ( 1 ) , projection: .ProjectionElems ) ) , operandCopy ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ) ) ) , span: span ( 56 ) )  statement (... kind: statementKindAssign (... place: place (... local: local ( 4 ) , projection: .ProjectionElems ) , rvalue: rvalueUse ( operandCopy ( place (... local: local ( 6 ) , projection: projectionElemField ( fieldIdx ( 0 ) , ty ( 23 ) )  .ProjectionElems ) ) ) ) , span: span ( 57 ) )  statement (... kind: statementKindAssign (... place: place (... local: local ( 5 ) , projection: .ProjectionElems ) , rvalue: rvalueUse ( operandCopy ( place (... local: local ( 6 ) , projection: projectionElemField ( fieldIdx ( 1 ) , ty ( 21 ) )  .ProjectionElems ) ) ) ) , span: span ( 58 ) )  statement (... kind: statementKindStorageDead ( local ( 6 ) ) , span: span ( 59 ) )  statement (... kind: statementKindStorageDead ( local ( 4 ) ) , span: span ( 55 ) )  .Statements , terminator: terminator (... kind: terminatorKindSwitchInt (... discr: operandCopy ( place (... local: local ( 5 ) , projection: .ProjectionElems ) ) , targets: switchTargets (... branches: branch ( 0 , basicBlockIdx ( 2 ) )  .Branches , otherwise: basicBlockIdx ( 1 ) ) ) , span: span ( 54 ) ) )  basicBlock (... statements: .Statements , terminator: terminator (... kind: terminatorKindCall (... func: operandConstant ( constOperand (... span: span ( 60 ) , userTy: noUserTypeAnnotationIndex , const: mirConst (... kind: constantKindZeroSized , ty: ty ( 24 ) , id: mirConstId ( 7 ) ) ) ) , args: operandConstant ( constOperand (... span: span ( 61 ) , userTy: noUserTypeAnnotationIndex , const: mirConst (... kind: constantKindAllocated ( allocation (... bytes: b"\x00\x00\x00\x00\x00\x00\x00\x00C\x00\x00\x00\x00\x00\x00\x00" , provenance: provenanceMap (... ptrs: provenanceMapEntry (... provSize: 0 , allocId: allocId ( 0 ) )  .ProvenanceMapEntries ) , align: align ( 8 ) , mutability: mutabilityMut ) ) , ty: ty ( 25 ) , id: mirConstId ( 8 ) ) ) )  .Operands , destination: place (... local: local ( 3 ) , projection: .ProjectionElems ) , target: noBasicBlockIdx , unwind: unwindActionUnreachable ) , span: span ( 62 ) ) )  basicBlock (... statements: .Statements , terminator: terminator (... kind: terminatorKindReturn , span: span ( 63 ) ) )  .BasicBlocks , locals: localDecl (... ty: ty ( 1 ) , span: span ( 64 ) , mut: mutabilityMut )  localDecl (... ty: ty ( 23 ) , span: span ( 65 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 23 ) , span: span ( 65 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 26 ) , span: span ( 62 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 23 ) , span: span ( 57 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 21 ) , span: span ( 58 ) , mut: mutabilityNot )  localDecl (... ty: ty ( 27 ) , span: span ( 56 ) , mut: mutabilityMut )  .LocalDecls , argCount: 2 , varDebugInfo: varDebugInfo (... name: symbol ( "lhs" ) , sourceInfo: sourceInfo (... span: span ( 65 ) , scope: sourceScope ( 0 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 1 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 1 ) )  varDebugInfo (... name: symbol ( "rhs" ) , sourceInfo: sourceInfo (... span: span ( 65 ) , scope: sourceScope ( 0 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 2 ) )  varDebugInfo (... name: symbol ( "self" ) , sourceInfo: sourceInfo (... span: span ( 66 ) , scope: sourceScope ( 1 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 1 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 1 ) )  varDebugInfo (... name: symbol ( "rhs" ) , sourceInfo: sourceInfo (... span: span ( 67 ) , scope: sourceScope ( 1 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 2 ) , projection: .ProjectionElems ) ) , argumentIndex: someInt ( 2 ) )  varDebugInfo (... name: symbol ( "a" ) , sourceInfo: sourceInfo (... span: span ( 57 ) , scope: sourceScope ( 2 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 4 ) , projection: .ProjectionElems ) ) , argumentIndex: noInt )  varDebugInfo (... name: symbol ( "b" ) , sourceInfo: sourceInfo (... span: span ( 58 ) , scope: sourceScope ( 2 ) ) , composite: noVarDebugInfoFragment , value: varDebugInfoContentsPlace ( place (... local: local ( 5 ) , projection: .ProjectionElems ) ) , argumentIndex: noInt )  .VarDebugInfos , spreadArg: noLocal , span: span ( 68 ) ) ) )
    )
  </functions>

  requires // i16 invariants
             0 -Int (1 <<Int 15) <=Int A
     andBool A <Int (1 <<Int 15)
     andBool 0 -Int (1 <<Int 15) <=Int B
     andBool B <Int (1 <<Int 15)
     // invariant of the `unchecked_add` operation
     andBool A +Int B <Int (1 <<Int 15) 
     andBool 0 -Int (1 <<Int 15) <=Int A +Int B 

endmodule
