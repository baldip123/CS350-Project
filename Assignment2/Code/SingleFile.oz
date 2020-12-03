
declare QuickSort Filter Map Append FoldR

%===============
% return the list of elements of Xs
% which satisfy the Boolean unary predicate P
% the elements will be in the same order as in Xs
%===============
fun {Filter Xs P}
   case Xs
   of nil then nil
   [] X|Xr then
      if {P X}
      then X|{Filter Xr P}
      else {Filter Xr P}
      end
   end
end

proc {Map Xs F ?Ys}
   case Xs
   of nil then Ys=nil
   [] X|Xr then Ys={F X}|{Map Xr F}
   end
end


fun {Append Xs Ys}
   case Xs
   of nil then Ys
   [] X|Xr then X|{Append Xr Ys}
   end
end

proc {FoldR Xs P Partial ?Ys}
   case Xs
   of nil then Ys=Partial
   [] X|Xr then Ys={P X {FoldR Xr P Partial}}
   end
end


%=============
% return the sort of Xs
%============
proc {QuickSort Xs LessThan  ?Ys}
   local
      FirstPart
      SecondPart
   in
      case Xs
      of nil then Ys=nil
      [] X|Xr then
	 FirstPart = {Filter  Xr fun {$ Y} {LessThan Y X} end}
	 SecondPart = {Filter  Xr fun {$ Y} {Not {LessThan Y X}}  end}
	 Ys={Append
	     {Append {QuickSort FirstPart LessThan} [X]}
	     {QuickSort SecondPart LessThan}}
      end
   end
end

declare
%==========
% Check if the entries in a *sorted* list
% are unique.
%==========
fun {HasUniqueEntries L}
   case L
   of H|T then
      case T
      of nil then true
      [] !H|T1 then false
      else {HasUniqueEntries T}
      end
   end
end

declare
%===========================
% equals Value.'<' if A and B are of the same type.
% Otherwise, any number is treated less than any literal.
%===========================
fun {MixedCompare A B}
   C D
in
   case A
   of literal(C)
   then
      case B
      of literal(D)
      then
	 if {IsNumber C}=={IsNumber D}
	 then C<D
	 else {IsNumber C} end
      end
   end
end

%=== Example Usage ===
% {Browse {HasUniqueEntries {Sort [a 1 2 d c 3] MixedCompare}}}
%=====================


declare
%==================
% The list of fieldname#value pairs can be specified in any
% order. The function returns a list of pairs sorted in the "arity"
% order - numerical fieldnames first, sorted in ascending order,
% followed by lexicographic fieldnames in alphabetical order.
%==================
fun {Canonize Pairs}
   Keys = {Map Pairs fun {$ X} X.1 end}
   SortedKeys = {QuickSort Keys MixedCompare}
   FindPairWithKey
   Result
in

   if {HasUniqueEntries SortedKeys}
   then
      %=======================
      % return unique K#value pair
      %=======================
      fun {FindPairWithKey K}
	 {Filter Pairs fun {$ Y} Y.1 == K end}.1
      end

      {Map SortedKeys FindPairWithKey}
   else illegalRecord(Pairs)
   end
end

declare SAS NumStoreVariables
SAS = {Dictionary.new}
{Cell.new 0 NumStoreVariables}

declare AddKeyToSAS RetrieveFromSAS BindRefToKeyInSAS BindValueToKeyInSAS PrintSAS

fun {AddKeyToSAS}
   local CurrKey in
      CurrKey =  @NumStoreVariables
      {Dictionary.put SAS CurrKey equivalence(CurrKey)}
      NumStoreVariables :=  (CurrKey+1)
      CurrKey
   end
end

fun {RetrieveFromSAS Key}
   %Note that UNIFY should take whether environment has the mapping for an identifier and should be a valid key
   local Value in
      Value = {Dictionary.get SAS Key}
      case Value
      of nil then nil %Just to make the syntax check go through
      []equivalence(K) then equivalence(K)
      []reference(K) then {RetrieveFromSAS K}
      else Value % will be record or literal or procedure as well
      end
   end
end

proc {BindRefToKeyInSAS Key RefKey}
   %Note that unify will guarantee that Key and Ref exist in SAS
   local Value RefValue in
      Value = {Dictionary.get SAS Key}
      RefValue = {Dictionary.get SAS RefKey}
      case Value of
	 equivalence(!Key) then skip
	 else {Raise badValueInBindRef(Key Value)}
      end
      case RefValue of
	 equivalence(!RefKey) then skip
	 else {Raise badValueInBindRef(RefKey RefValue)}
	%These case statements are here to enforce that the wa unfiy is calling these funtions is correct.
	%You can check SAS-reference for more details.
      end
      if Key == RefKey then skip
      else {Dictionary.put SAS Key reference(RefKey)}
      end
   end
end

proc {BindValueToKeyInSAS Key Val}
   local Value in
      Value = {Dictionary.get SAS Key}
      case Value
      of equivalence(!Key) then skip
      else {Raise badValueInBindVal(Key Value)}
      end
      {Dictionary.put SAS Key Val}
   end
end


proc {PrintSAS}
   {Browser.browse 'Printing Single Assignment Store'}
   {Browser.browse 'Number Of Variables'}
   {Browser.browse {Cell.access NumStoreVariables}}
   local PrintPair KeyList in
      fun {PrintPair Key}
	 {Browser.browse [Key {Dictionary.get SAS Key}]}
	 Key
      end
      KeyList = {Dictionary.keys SAS}
      {Browser.browse {Map KeyList PrintPair}}
   end
   {Browser.browse 'Done Printing'}
end

declare
proc {Unify Exp1 Exp2 Env}
   SubstituteIdentifiers
   WeakSubstitute
   UnifyRecursive
in
   %==================
   % Replace every identifier in the code with
   % (1) its key in the SAS store if it is unbound (or)
   % (2) with its value if it is bound [determined]
   % Code by Siddharth Agarwal
   %=================
   fun {SubstituteIdentifiers Exp Env}
      case Exp
      of [procedure A B C] then Exp
	  [] H|T then
	 {SubstituteIdentifiers H Env}|{SubstituteIdentifiers T Env}
      [] ident(X) then {RetrieveFromSAS Env.X}
      else Exp end
   end

   %=================
   % Used when unifying records. Similar to SubstituteIdentifiers,
   % except that lists are not unified.
   %=================
   fun {WeakSubstitute X}
      case X
      of equivalence(A) then {RetrieveFromSAS A}
      else X end
   end

   %=================
   % Main unification procedure.
   % Assumes that identifiers have been substituted away, by calling
   % SubstituteIdentifiers.
   %==================
   proc {UnifyRecursive Exp1 Exp2 UnificationsSoFar}
      Unifications % New list of unifications
   in
      %==================
      % Ensure that we do not go into an infinite loop
      % unifying already unified expressions.
      % Code modified from Siddharth Agarwal's code
      %==================
      if {List.member [Exp1 Exp2] UnificationsSoFar}
      then skip
      else
	 Unifications = {List.append [Exp1 Exp2] UnificationsSoFar}
	 case Exp1
	 of equivalence(X) then
	    case Exp2
	    of equivalence(Y) then {BindRefToKeyInSAS X Y}
	    else {BindValueToKeyInSAS X Exp2} end
	 [] literal(X) then
	    case Exp2
	    of equivalence(_) then
	       {UnifyRecursive Exp2 Exp1 Unifications}
	    [] literal(!X) then skip
	    else raise incompatibleTypes(Exp1 Exp2) end
	    end
	 [] record | L | Pairs1 then % not label(L)
	    case Exp2
	    of equivalence(_) then
	       {UnifyRecursive Exp2 Exp1 Unifications}
	    [] record|!L|Pairs2 then % recursively unify
	       Canon1 = {Canonize Pairs1.1}
	       Canon2 = {Canonize Pairs2.1}
	       CorrespondingFeaturesSame
	       HasSameArity
	    in
	       if {List.length Canon1} \= {List.length Canon2}
	       then raise incompatibleTypes(Exp1 Exp2) end
	       end
	       CorrespondingFeaturesSame={List.zip Canon1 Canon2
	       				  fun {$ Xs Ys} Xs.1==Ys.1 end}
	       HasSameArity = {FoldR  CorrespondingFeaturesSame fun {$ X Y} X andthen Y end true}
	       if HasSameArity == false
	       then raise incompatibleTypes(Exp1 Exp2) end
	       end
	       {List.zip Canon1 Canon2
		fun {$ X Y}
		   {UnifyRecursive
		    {WeakSubstitute X.2.1} {WeakSubstitute Y.2.1}
		    Unifications}
		   unit
		end
		_}
	    else raise incompatibleTypes(Exp1 Exp2) end
	    end %
	 else
	    raise incompatibleTypes(Exp1 Exp2) end
	 end
      end % if
   end % UnifyRecursive

   %========= Start Unification ======
   {UnifyRecursive {SubstituteIdentifiers Exp1 Env}
    {SubstituteIdentifiers Exp2 Env} nil}

end

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
                {Exception.'raise' secondArgumentNotBoundToLiteral(Y)}
            end
        else
            {Exception.'raise' firstArgumentNotBoundToLiteral(X)}
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
                {Exception.'raise' secondArgumentNotBoundToLiteral(Y)}
            end
        else
            {Exception.'raise' secondArgumentNotBoundToLiteral(X)}
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
  if {IsEmpty SemanticStack} then {PrintSAS} {Browse executionFinished}
  else
    {Browse @SemanticStack}
    {PrintSAS}
    {Browse executionStatePrinted}
    {Browse executionStatePrinted}
    {Browse proceedingToNextExecution}
    {Browse proceedingToNextExecution}
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

%TEST4.a Checking if environment reverts to old
%{Push SemanticStack semstate(st:[var ident(x) [[var ident(x) [nop]] [nop]]] env:env())}
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

%TEST 8.a
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) ident(y)] [bind ident(x) ident(z)] [bind ident(z) ident(y)]]]]] env:env())}
%{Interpret}

%3.Testing  VAR LITERAL Bind
%TEST 9
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [bind ident(x) literal(3)]]] env:env())}
%{Interpret}

%TEST 10
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) ident(y)] [bind ident(y) ident(z)] [bind ident(x) literal(3)]]]]] env:env())}
%{Interpret}

%TEST 10.a Failure Test
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) ident(y)] [bind ident(y) ident(z)] [bind ident(x) literal(3)] [bind ident(y) literal(a)]]]]] env:env())}
%{Interpret}

%4.Testing ADD MUL
%TEST 11
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) literal(3)] [add ident(z) ident(x) literal(3)]]]]] env:env())}
%{Interpret}

%TEST 11.a Failure Case
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) literal(3)] [add ident(z) ident(y) literal(3)]]]]] env:env())}
%{Interpret}


%TEST 12
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) literal(3)] [bind ident(y) literal(7)] [mul ident(z) ident(x) ident(y)]]]]] env:env())}
%{Interpret}

%TEST 12.a Failure, as z is already bound to a value
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(x) literal(3)] [bind ident(z) literal(20)] [bind ident(y) literal(7)] [mul ident(z) ident(x) ident(y)]]]]] env:env())}
%{Interpret}


%5.Testing records
%TEST 13
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) [var ident(z) [[bind ident(z) [record literal(a) [[literal(1) ident(x)]]]] [bind ident(z) [record literal(a) [[literal(1) ident(y)]]]]]]]] env:env())}
%{Interpret}

%TEST 14 - Circular records
%{Push SemanticStack semstate(st:[var ident(x) [bind ident(x) [record literal(list) [[literal(1) literal(1)] [literal(2) ident(x)]] ] ]] env:env())}
%{Interpret}

%TEST 14.a - Circular Records 2
%X = 1|Y
%Y = 1|X
%declare S
%S = [[bind ident(x) [record literal(list) [[literal(1) literal(1)] [literal(2) ident(y)]]]] [bind ident(y) [record literal(list) [[literal(1) literal(1)] [literal(2) ident(x)]]]] ]
%{Push SemanticStack semstate(st:[var ident(x) [var ident(y) S ]] env:env())}
%{Interpret}


%4.c Testing function values
%TEST 15
%{Push SemanticStack semstate(st:[[var ident(x) [[
%                                                  [bind ident(x) [procedure [ident(x1) ident(x2) ident(x3)] [
%                                                                                                         [add ident(x1) ident(x2) ident(x3)]
%                                                                                                        ]]]
%                                                 ]]]] env:env())}
%{Interpret}

%TEST 15.1 Closure for Bind to Record in a procedure, you can change identifier for hitting different braches
%declare ProcVal RecordVal
%RecordVal = [record literal(a) [[literal(1) ident(z3)]]]
%ProcVal = [procedure [ident(x1) ident(x2)] [bind ident(x1) RecordVal]]
%{Push SemanticStack semstate(st:[var ident(x)
%				 [var ident(y)
%				  [var ident(z)
%				   [bind ident(z) ProcVal]
%				  ]
%				 ]
%				]    env:env())}
%{Interpret}

%TEST 15.2 Closure for Bind with var in it
%declare ProcVal = [procedure [ident(x)] [var ident(y) [bind ident(x1) ident(y)]]]
%{Push SemanticStack semstate(st:[var ident(x)
%				 [var ident(y)
%				  [var ident(z)
%				   [bind ident(z) ProcVal]
%				  ]
%				 ]
%				]    env:env())}
%{Interpret}


%TEST 15.3 Closure for apply
%declare ProcVal
%declare ProcVal2
% ProcVal =  [procedure [ident(x1)] [var ident(y) [bind ident(x1) ident(y)]]]
%ProcVal2 = [procedure [ident(x2)] [apply ident(z) ident(x2)]]
%{Push SemanticStack semstate(st:[var ident(x)
%				 [var ident(y)
%				  [var ident(z)
%				   [
%				    [bind ident(z) ProcVal]
%				    [var ident(t) [bind ident(t) ProcVal2]]
%				   ]
%				  ]
%				 ]
%				]    env:env())}
%{Interpret}

%TEST 15.4 Closure for compound statements in apply
%declare ProcVal
%declare ProcVal2
% ProcVal =  [procedure [ident(x1)] [var ident(y) [[bind ident(x1) ident(y)] [bind ident(x1) ident(x)]]   ]]
%ProcVal2 = [procedure [ident(x2)] [apply ident(z) ident(x2)]]
%{Push SemanticStack semstate(st:[var ident(x)
%				 [var ident(y)
%				  [var ident(z)
%				   [
%				    [bind ident(z) ProcVal]
%				    [var ident(t) [bind ident(t) ProcVal2]]
%				   ]
%				  ]
%				 ]
%				]    env:env())}
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

%TEST18
%{Push SemanticStack semstate(st:[var ident(x)
%                                              [
%                                                   [bind ident(x) [record literal(a) [[literal(c) literal(3)] [literal(b) literal(2)]]] ]
%                                                   [match ident(x) [record literal(a)
%                                                                   [[literal(b) ident(p)] [literal(c) ident(q)] ]] [nop] [nop]
%                                                    ]
%                                              ]
%                                 ]
%                                 env:env())}
%{Interpret}

%TEST19
%{Push SemanticStack semstate(st:[var ident(x)
%                                              [
%                                                   [bind ident(x) [record literal(a) [[literal(c) literal(3)] [literal(b) literal(2)][literal(d) literal(5)]]] ]
%                                                   [match ident(x) [record literal(a)
%                                                                   [[literal(b) ident(p)] [literal(c) ident(q)] ]] [nop] [nop]
%                                                    ]
%                                              ]
%                                 ]
%                                 env:env())}
%{Interpret}

%TEST20
%{Push SemanticStack semstate(st:[var ident(x)
%                                              [
%                                                   [match ident(x) [record literal(a)
%                                                                   [[literal(b) ident(p)] [literal(c) ident(q)] ]] [nop] [nop]
%                                                    ]
%                                              ]
%                                 ]
%                                 env:env())}
%{Interpret}

%TEST21
%{Push SemanticStack semstate(st:[var ident(x)[ var ident(y) [ var ident(z)
%                                              [
%                                                   [bind ident(x) [record literal(a) [[literal(c) ident(y)] [literal(b) ident(z)]] ]]
%                                                   [match ident(x) [record literal(a)
%                                                                   [[literal(b) ident(p)] [literal(c) ident(q)] ]] [nop] [nop]
%                                                    ]
%                                              ]
%                                 ]]]
%                                 env:env())}
%{Interpret}

%TEST22
%{Push SemanticStack semstate(st:[var ident(x)
%                                              [
%                                                   [bind ident(x) [record literal(a) [[literal(b) [record literal(k) [[literal(d) literal(2)] [literal(e) literal(3)]]]] [literal(c) literal(3)]]] ]
%                                                   [match ident(x) [record literal(a)
%                                                                   [[literal(b) ident(p)] [literal(c) ident(q)] ]] [nop] [nop]
%                                                    ]
%                                              ]
%                                 ]
%                                 env:env())}
%{Interpret}

%TEST23
%{Push SemanticStack semstate(st:[var ident(x)[ var ident(y) [var ident(z)
%                                              [
%                                                   [bind ident(x) [record literal(a) [[literal(b) [record literal(k) [[literal(d) literal(2)] [literal(e) literal(3)]]]] [literal(c) literal(3)]]] ]
%                                                   [match ident(x) [record literal(a)
%                                                                   [[literal(b) ident(p)] [literal(c) ident(q)] ]] [bind ident(y) literal(8)] [bind ident(z) literal(7)]
%                                                    ]
%                                              ]
%                                 ]]]
%                                 env:env())}
%{Interpret}

%TEST24
%{Push SemanticStack semstate(st:[var ident(x)[ var ident(y) [var ident(z)
%                                              [
%                                                   [bind ident(x) [record literal(b) [[literal(b) [record literal(k) [[literal(d) literal(2)] [literal(e) literal(3)]]]] [literal(c) literal(3)]]] ]
%                                                   [match ident(x) [record literal(a)
%                                                                   [[literal(b) ident(p)] [literal(c) ident(q)] ]] [bind ident(y) literal(8)] [bind ident(z) literal(7)]
%                                                    ]
%                                              ]
%                                 ]]]
%                                 env:env())}
%{Interpret}

%6.Tests for function application
%TEST25
%{Push SemanticStack statement(st:[var ident(q) [ [bind ident(q) literal(10)] [var ident(x) [var ident(z) [[bind ident(z) [procedure [ident(y)] [bind ident(x) ident(y)]]] [apply ident(z) ident(q)]]]]]] env:env())}
%{Interpret}
