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
