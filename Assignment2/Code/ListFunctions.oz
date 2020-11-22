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
   {Browser.browse map#Xs}
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

{Browser.browse {QuickSort  [7 6 1 3 5] fun {$ X Y} X<Y end}}

