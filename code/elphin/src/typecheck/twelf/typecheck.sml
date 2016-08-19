structure TypeCheckLF =
  TypeCheckLF ((*! structure IntSyn' = IntSyn !*)
	     structure Conv = Conv
	     structure Whnf = Whnf
	     structure Names = Names
	     structure Print = Print);
