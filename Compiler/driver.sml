structure Parse =
struct 
  fun parse filename =
      let val file = TextIO.openIn filename
	  fun get _ = TextIO.input file
	  val lexer = Mlex.makeLexer get
	  fun do_it() =
	      let val t = lexer()
	       in print t; print "\n";
		   case substring(t,0,3) of
				"EOF" => ()
				| "ERR" => ()
				| _ => do_it()
	      end
       in do_it();
	  TextIO.closeIn file
      end

end

