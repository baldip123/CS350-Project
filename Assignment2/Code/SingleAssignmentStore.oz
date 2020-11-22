
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

