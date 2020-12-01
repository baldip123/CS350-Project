\insert 'SingleAssignmentStore.oz'
\insert 'Unify.oz'

declare Push Pop IsEmpty SemanticStack Execute Interpret HandleNop AdjoinEnv HandleVar
SemanticStack = {Cell.new nil}

fun {Add X Y Env}
    local Val1 Val2 in
        case X of nil then {Exception.'raise' firstArgumentNil}
        [] ident(A) then
            Val1 = {RetrieveFromSAS Env.A}
        [] literal(A) then
            Val1 = literal(A)
        else
         {Exception.'raise' firstArgumentNotAnIdentfier}
        end
        case Y of nil then {Exception.'raise' secondArgumentNil}
        [] ident(B) then
            Val2 = {RetrieveFromSAS Env.B}
        [] literal(A) then
            Val2 = literal(A)
        else
         {Exception.'raise' secondArgumentNotAnIdentfier}
        end
        case Val1 of nil then nil
        []literal(B) then
            case Val2 of nil then nil
            []literal(C) then
                literal(B+C)
            else
                {Exception.'raise' secondArgumentUnbound}
            end
        else
            {Exception.'raise' firstArgumentUnbound}
        end
    end
end

fun {Mul X Y Env}
    local Val1 Val2 in
        case X of nil then {Exception.'raise' firstArgumentNil}
        [] ident(A) then
            Val1 = {RetrieveFromSAS Env.A}
        [] literal(A) then
            Val1 = literal(A)
        else
         {Exception.'raise' firstArgumentNotAnIdentfier}
        end
        case Y of nil then {Exception.'raise' secondArgumentNil}
        [] ident(B) then
            Val2 = {RetrieveFromSAS Env.B}
        [] literal(A) then
            Val2 = literal(A)
        else
         {Exception.'raise' secondArgumentNotAnIdentfier}
        end
        case Val1 of nil then nil
        []literal(B) then
            case Val2 of nil then nil
            []literal(C) then
                literal(B*C)
            else
                {Exception.'raise' secondArgumentNotLiteral}
            end
        else
            {Exception.'raise' firstArgumentNotLiteral}
        end
    end
end

fun {AdjoinEnv Old Id Key}
    local NewEnv in
        NewEnv = env(Id:Key)
        {Adjoin Old NewEnv}
    end
end

proc {Push Stack Statement}
    local Temp in
      Temp = Statement|@Stack
      Stack := Temp
    end
end

fun {Pop Stack}
  case @Stack of nil then {Exception.'raise' stackPoppedWhileEmpty}
  []H|T then
    Stack := T
    H
  end
end

fun {IsEmpty Stack}
  @Stack == nil
end

proc {HandleNop}
  skip
end

proc {HandleVar Statement Environment}
  local NewKey NewEnvironment NewStatement Identifier in
    Identifier = Statement.2.1.1
    NewKey = {AddKeyToSAS}
    NewEnvironment = {AdjoinEnv Environment Identifier NewKey}
    NewStatement = Statement.2.2.1
    {Push SemanticStack semstate(st:NewStatement env:NewEnvironment)}
  end
end

fun {SetDifference SetA SetB}
  {Record.subtractList SetA {Record.arity SetB}}
end

fun {ComputeFreeVariableSetInProcedure ParamListWithIdent ProcedureStatement}
  %Check if formal parameters are unique(len of remove duplicate must be equal to length of normal)
  local ParamList in
  %note that ParamListWithIdent will have [ident(x) ident(y)....] an d param list will have [x y ...]
    ParamList = {Map ParamListWithIdent fun {$ X} X.1 end}
    if {Length ParamList} == {Length {RemoveDuplicates ParamList}} then
      local SetOfParams FreeVariableSet ProcedureStatementFreeVariableSet in
        ProcedureStatementFreeVariableSet = {ComputeFreeVariableSet ProcedureStatement}
        %Note that ParamList is already checked to be unique
        SetOfParams = {Record.make set ParamList}
        FreeVariableSet = {SetDifference ProcedureStatementFreeVariableSet SetOfParams}
        FreeVariableSet
      end
    else {Exception.'raise' paramsNotDistinctInFunction(ParamList)}
    end
  end
end

fun {ElimDuplicatesInSorted Xs}
   case Xs
   of nil then nil
   []H|T then
      case T
      of nil then H|nil
      []H1|T1 then if H==H1 then {ElimDuplicatesInSorted T}
		   else H|{ElimDuplicatesInSorted T}
		   end
      end
   end
end

fun {RemoveDuplicates Xs}
  local SortedXs in
    SortedXs = {Sort Xs Value.'<'}
    {ElimDuplicatesInSorted SortedXs}
  end
end

fun {ComputeFreeVariablesInRecord RecordAST}
  %RecordAST is of form [record Label Features]
  %output is of form set(x:1 y:1 z:1....), basically all features are the set of free variables and all values are 1
  local FreeVariableSet FreeVariableList Pairs in
    Pairs = RecordAST.2.2.1
    %Each pair will be of type [literal(X) ident(Y)], hence .2.1.1 will be Y
    %note that I dont really care about the field(which were supposed to be 1, I only care about the features which are the variables)
    FreeVariableList = {Map Pairs fun {$ X} X.2.1.1 end}
    %Note that Duplicates will have to be removed
    FreeVariableSet = {Record.make set {RemoveDuplicates FreeVariableList}}
    FreeVariableSet
  end
end


fun {ComputeFreeVariableSet Statement}
  case Statement of nil then set()
  else
    case Statement.1
      of nil then set()
      [] nop then set()
      %Statement.2.2.1 is the statement in var Statement.2.1.1 is X(and not ident X) if [var ident(X)]
      [] var then {SetDifference {ComputeFreeVariableSet Statement.2.2.1} {Record.make set [Statement.2.1.1]}} %second element is the single set
      [] bind then
        case Statement of
          %Note that the varibles must be fatures for correct computations, also note that records can't have duplicate keys
          nil then set()
          [] [bind ident(Var1) ident(Var2)] then {Record.make set {RemoveDuplicates [Var1 Var2]}}
          [] [bind ident(Var) literal(X)] then set(Var:1)
          [] [bind ident(Var) [record Label Pairs]] then {Adjoin set(Var:1) {ComputeFreeVariablesInRecord [record Label Pairs]}}
          [] [bind ident(Var) [procedure ParamList ProcedureStatement]] then {Adjoin set(Var:1) {ComputeFreeVariableSetInProcedure  ParamList ProcedureStatement}}
        end
      [] X|Xs then {Adjoin {ComputeFreeVariableSet Statement.1} {ComputeFreeVariableSet Statement.2} }
      [] add then
        case Statement of
          nil then set()
          [] [add ident(Z) ident(X) ident(Y)] then {Record.make set {RemoveDuplicates [Z X Y]}}
          [] [add ident(Z) literal(X) ident(Y)] then {Record.make set {RemoveDuplicates [Z Y]}}
          [] [add ident(Z) ident(X) literal(Y)] then {Record.make set {RemoveDuplicates [Z X]}}
          [] [add ident(Z) literal(X) literal(Y)] then {Record.make set {RemoveDuplicates [Z]}}
        end
      [] mul then
        case Statement of
          nil then set()
          [] [mul ident(Z) ident(X) ident(Y)] then {Record.make set {RemoveDuplicates [Z X Y]}}
          [] [mul ident(Z) literal(X) ident(Y)] then {Record.make set {RemoveDuplicates [Z Y]}}
          [] [mul ident(Z) ident(X) literal(Y)] then {Record.make set {RemoveDuplicates [Z X]}}
          [] [mul ident(Z) literal(X) literal(Y)] then {Record.make set {RemoveDuplicates [Z]}}
        end
      [] apply then
        local IdentifierList FreeVariableSet in
          %[apply ident(f) ident(x1) ... ident(xn)]
          %note that I'll be allowing only identifiers, otherwise this code may fail
          %Stament.2 is [ident(f) ident(x1) ... ident(xn)]
          %IdentifierList will be [f x1 ... xn]
          IdentifierList = {Map Statement.2 fun {$ X} X.1 end}
          FreeVariableSet = {Record.make set {RemoveDuplicates IdentifierList}}
          FreeVariableSet
        end
      [] match then
      %[match ident(x) p s1 s2] this is AST for match
        case Statement of
          nil then set()
          [] [match ident(X) PatternRecord MatchStatement NotMatchStatement] then
                  {Adjoin
                    {Adjoin set(X:1) {ComputeFreeVariableSet NotMatchStatement}}%(X U Free(S2))
                    {SetDifference {ComputeFreeVariableSet MatchStatement} {ComputeFreeVariablesInRecord PatternRecord}}%(Free(S1) -Free(P))
                  }
        end
    end
  end
end

fun {GetStoreVar Environment Identifier}
  %Note that here Identifier will x and not ident x
  if {Value.hasFeature Environment Identifier} then {Value.condSelect Environment Identifier nil}
  else {{Exception.'raise' variableNotIntroduce(Identifier)}}
  end
end

fun {RestrictEnvironment Environment FreeVariableSet}
  %Environment is a record of form (x:store_variable_number)
  %FreeVaribleSet is of the form (x:_ y:_).....where x and y are free variable
  local RestrictedEnv FreeVarList in
    FreeVarList = {Arity FreeVariableSet}
    %{List.toRecord f [a#1 b#2 c#3]} returns f(a: 1 b: 2 c: 3).
    RestrictedEnv = {List.toRecord env ({Map FreeVarList fun {$ Identifier} (Identifier#{GetStoreVar Environment Identifier}) end}) }
    RestrictedEnv
  end
end

fun {ComputeClosure ProcedureAST Environment}
  local ParamList ProcedureStatement ContextualEnvironment FreeVariableSet in
    ParamList = ProcedureAST.2.1
    ProcedureStatement = ProcedureAST.2.2.1
    %implelent this set difference
    FreeVariableSet = {ComputeFreeVariableSetInProcedure ParamList ProcedureStatement}
    ContextualEnvironment = {RestrictEnvironment Environment FreeVariableSet}
    %returns the closure
    [procedure ParamList ProcedureStatement ContextualEnvironment]
  end
end

proc {HandleBind Statement Environment}
  case Statement of
    nil then skip % Just to make syntax check go through
    [] [bind ident(Var1) ident(Var2)] then {Unify ident(Var1) ident(Var2) Environment}
    [] [bind ident(Var) literal(X)] then {Unify ident(Var) literal(X) Environment}
    [] [bind ident(Var) [record Label Features]] then {Unify ident(Var) [record Label Features] Environment}
    [] [bind ident(Var) [procedure ParamList ProcedureStatement]] then {Unify ident(Var) {ComputeClosure [procedure ParamList ProcedureStatement] Environment} Environment}
  end
end

proc {HandleAdd Statement Environment}
  case Statement of nil then skip
   [] [add ident(Target) X Y] then {Unify ident(Target) {Add X Y Environment} Environment} % X,Y can be literal also
  end
end

proc {HandleMul Statement Environment}
  case Statement of nil then skip
   [] [mul ident(Target) X Y] then {Unify ident(Target) {Mul X Y Environment} Environment} % X,Y can be literal also
  end
end

proc {HandleApply Statement Environment}
  %{FX1...Xn}is represented in our syntax by[apply ident(f) ident(x1) ... ident(xn)]
  %We already know that the statement list will be not nill
  %Also remember it is not necessary that the function call will have params,
    %so list have mave only the function name.
  %Finally only identifiers are allowed in my syntax in function calls
  case Statement.2 of nil then {Exception.'raise' functionNameNotGiven}
   [] ident(FunctionIdent)|ActualParamList then
      %Function ident will be f, and not ident(f), due to pattern match
      %ParamList will be [ident(x1) .. (xn)], It can be nill as well
     local FunctionIdentValue in
      %1. Find if f is in the environment
      if {Value.hasFeature Environment FunctionIdent} then
        %2. Find if f is determined and is bound to procedure value
        FunctionIdentValue = {RetrieveFromSAS Environment.FunctionIdent}
        case FunctionIdentValue of nil then {Exception.'raise' notAFunctionBindind(FunctionIdent)}
          [] [procedure FormalParamList ProcedureStatement ContextualEnv] then
            %3. Check the arity of application
            if {Length ActualParamList} \= {Length FormalParamList} then {Exception.'raise' wrongNumberOfArgsInFunctionApllication(Statement)}
            else
              %4.Arity Check passed, Push the statement
              local ProcedureEnvironment FormalParamListWithEnvironmentMap in
                FormalParamListWithEnvironmentMap =  {List.zip FormalParamList ActualParamList (fun {$ FormalParam ActualParam} FormalParam.1#(Environment.(ActualParam.1))end)}
                ProcedureEnvironment = {Adjoin ContextualEnv {List.toRecord env FormalParamListWithEnvironmentMap}}
                {Push SemanticStack semstate(st:ProcedureStatement env:ProcedureEnvironment)}
              end
            end
          else {Exception.'raise' notAFunctionBindind(FunctionIdent)}
        end
      else {Exception.'raise' notDeclared(FunctionIdent)}
      end
    end
  end
end



fun {PatternMatch X P Env}
  local Val Canon1 Canon2 CorrespondingFeaturesSame HasSameArity in
    case X of nil then Val = nil
    [] ident(A) then
      %Check if Env.A will fail.
      Val = {RetrieveFromSAS Env.A}
    else
     {Exception.'raise' argumentNotAnIdentfier}
    end
    case Val of nil then false
    [] equivalence(A) then {Exception.'raise' variableUnbound}
    [] record|Label1|Features1|nil then
      case P of nil then false
      [] record|Label2|Features2|nil then
        if Label2 == Label1 then
	    Canon1 = {Canonize Features1}
	    Canon2 = {Canonize Features2}
	    CorrespondingFeaturesSame={List.zip Canon1 Canon2
	       				  fun {$ Xs Ys} Xs.1==Ys.1 end}
      HasSameArity = {FoldR  CorrespondingFeaturesSame fun {$ X Y} X andthen Y end true}
            if HasSameArity then true
            else false
            end
        else false
        end
      else false
      end
    else false
    end
  end
end

fun {AddValue F1 F2}
  case F2.2.1 of ident(X) then
    local NewKey Value in
      NewKey = {AddKeyToSAS}
      case F1.2.1 of equivalence(A) then
        {BindRefToKeyInSAS NewKey A}
        X#NewKey
      [] reference(A) then
        {BindRefToKeyInSAS NewKey A}
        X#NewKey
      [] literal(A) then
        {BindValueToKeyInSAS NewKey literal(A)}
        X#NewKey
      %It can be record as well
      [] record|T then
        {BindValueToKeyInSAS NewKey F1.2.1}
        X#NewKey
      else {Exception.'raise' featureOneNotIdentified}
      end
    end

  else {Exception.'raise' valueTwoNotAnIdentifier}

  end
end

proc {AdjoinPatternEnv Env X P NewEnv}
  local Val Canon1 Canon2 in
    case X of nil then Val = nil
    [] ident(A) then Val = {RetrieveFromSAS Env.A}
    else Val = nil
    end
    case Val of nil then skip
    [] record|Label1|Features1|nil then
      case P of nil then skip
      [] record|Label2|Features2|nil then
      Canon1 = {Canonize Features1}
	    Canon2 = {Canonize Features2}
      %This should put the features and values in order, otherwise they may be out of order, even for matching records.
      {AdjoinList Env {List.zip Canon1 Canon2 AddValue} NewEnv}
      else skip
      end
    end
  end
end

proc {HandleMatch Statement Environment}
  case Statement of nil then skip
  [] [match ident(X) P S1 S2] then
    if {PatternMatch ident(X) P Environment} then
      local NewEnv in
        {AdjoinPatternEnv Environment ident(X) P NewEnv}
        {Push SemanticStack semstate(st:S1 env:NewEnv)}
      end
    else
      {Push SemanticStack semstate(st:S2 env:Environment)}
    end
  end
end

proc {Execute SemanticStatement}
%Note that this ensures that only non-nil statements are pushed onto the stack
  local Statement Environment in
    %
    Statement =  SemanticStatement.st
    Environment = SemanticStatement.env
    case Statement.1 of
      nil then skip
      [] nop then {HandleNop}
      [] var then {HandleVar Statement Environment}
      [] bind then {HandleBind Statement Environment}
      [] X|Xs then if Statement.2 \= nil then
                      %makes sure that only non-nil statements are pushed onto the stack
                      {Push SemanticStack semstate(st:Statement.2 env:Environment)}
                   end
                   {Push SemanticStack semstate(st:Statement.1 env:Environment)}
      [] add then {HandleAdd Statement Environment} % X,Y can be literal also
      [] mul then {HandleMul Statement Environment} % X,Y can be literal also
      [] apply then {HandleApply Statement Environment}
      [] match then {HandleMatch Statement Environment}
    end
  end
end

proc {Interpret}
   {Browse calledInterPret}
  %Skip when the stack is empty
  if {IsEmpty SemanticStack} then {Browse executionFinished}
  else
    {Browse @SemanticStack}
    {PrintSAS}
    {Browse a}
    {Browse a}
    {Browse a}
    {Browse a}
    local SemanticStatement in
      %POP THE STACK
       SemanticStatement = {Pop SemanticStack}
      %EXECUTE THE STATEMENT
      {Execute SemanticStatement}
      %KEEP EXECUTING TILL STACK IS EMPTY
      %CALL INTERPRET AGAIN
      {Interpret}
    end
  end
end

%1.Testing NOP
%TEST 1
%{Push SemanticStack semstate(st:[nop] env:env())}
%{Interpret}

%TEST 2
%{Push SemanticStack semstate(st:[[nop] [nop] [nop]] env:env())}
%{Interpret}

%2.Testing Var
%TEST 3
%{Push SemanticStack semstate(st:[var ident(x) [nop]] env:env())}
%{Interpret}

%TEST 4
%{Push SemanticStack semstate(st:[var ident(x) [var ident(x) [nop]]] env:env())}
%{Interpret}

%TEST 5
%{Push SemanticStack semstate(st:[var ident(x) [var ident(x) [[nop] [nop]]]] env:env())}
%{Interpret}

%3.Testing  VAR VAR Bind
%TEST 6
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [bind ident(x) ident(y)]]] env:env())}
%{Interpret}

%TEST 7
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) ident(y)] [bind ident(y) ident(z)]]]]] env:env())}
%{Interpret}

%TEST 8
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) ident(y)] [bind ident(y) ident(z)] [bind ident(z) ident(x)]]]]] env:env())}
%{Interpret}

%3.Testing  VAR LITERAL Bind
%TEST 9
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [bind ident(x) literal(3)]]] env:env())}
%{Interpret}

%TEST 10
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) ident(y)] [bind ident(y) ident(z)] [bind ident(x) literal(3)]]]]] env:env())}
%{Interpret}

%4.Testing ADD MUL
%TEST 11
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) literal(3)] [add ident(z) ident(x) literal(3)]]]]] env:env())}
%{Interpret}

%TEST 12
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) literal(3)] [bind ident(y) literal(7)] [mul ident(z) ident(x) ident(y)]]]]] env:env())}
%{Interpret}

%5.Testing records
%TEST 13
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(z) [record literal(a) [[literal(1) ident(x)]]]] [bind ident(z) [record literal(a) [[literal(1) ident(y)]]]]]]]] env:env())}
%{Interpret}



%4.c Testing function values
%TEST 15
%{Push SemanticStack semstate(st:[[var ident(x) [[
%                                                  [bind ident(x) [procedure [ident(x1) ident(x2) ident(x3)] [
%                                                                                                         [add ident(x1) ident(x2) ident(x3)]
%                                                                                                        ]]]
%                                                 ]]]] env:env())}
%{Interpret}



%TEST 15
%Should Give Failure as Y is unbound
%{Push SemanticStack semstate(st:[[var ident(x) [[
%                                                  [bind ident(x) [procedure [ident(x1) ident(x2) ident(x3)] [
%                                                                                                         [add ident(x1) ident(x2) ident(x3)]
%                                                                                                        ]]]
%                                                  [var ident(y) [
%                                                                  [var ident(z) [
%                                                                                 [var ident(a) [
%                                                                                                [bind ident(a) literal(69)]
%                                                                                                [bind ident(z) literal(31)]
%                                                                                                [apply ident(x) ident(a) ident(z) ident(y)]
%                                                                                              ]]
%                                                                               ]]
%                                                                ]]
%                                                 ]]]] env:env())}
%{Interpret}


%TEST 16
%{Push SemanticStack semstate(st:[[var ident(x) [[
%                                                  [bind ident(x) [procedure [ident(x1) ident(x2) ident(x3)] [
%                                                                                                         [add ident(x1) ident(x2) ident(x3)]
%                                                                                                        ]]]
%                                                  [var ident(y) [
%                                                                  [var ident(z) [
%                                                                                 [var ident(a) [
%                                                                                                [bind ident(y) literal(69)]
%                                                                                                [bind ident(z) literal(31)]
%                                                                                                [apply ident(x) ident(a) ident(z) ident(y)]
%                                                                                              ]]
%                                                                               ]]
%                                                                ]]
%                                                 ]]]] env:env())}
%{Interpret}

%6.Pattern Match
%TEST17
%{Push SemanticStack semstate(st:[var ident(x)
%                                              [
%                                                   [bind ident(x) [record literal(a) [[literal(b) literal(2)] [literal(c) literal(3)]]] ]
%                                                   [match ident(x) [record literal(a)
%                                                                   [[literal(b) ident(p)] [literal(c) ident(q)] ]] [nop] [nop]
%                                                    ]
%                                              ]
%                                 ]
%                                 env:env())}
%{Interpret}

%Also checked for cases where a)label is different, b)features are different c)features are same but in diff orders
%NOW CHECK FOR CASES WHICH VERIFY THAT ENVIRONMENT IS BEING PASSED ON CORRECTLY
