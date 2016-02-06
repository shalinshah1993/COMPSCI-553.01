type pos = int
type lexresult = Tokens.token

(* Keep a check on Nested String/Comments*)
val nestedComment = ref 0
val nestedString = ref 0

(* Keep a check on Escape CHAR by saving string *)
val current_string : char list ref = ref []
val string_start_pos = ref 0

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

(* This gets called when lex reaches EOF *)
fun eof() = 
	if (!nestedComment) = 0 then
		let 
			val pos = hd(!linePos); 
		in 
			if (!nestedString) = 0 then
				Tokens.EOF(pos,pos) 
			else
				(ErrorMsg.error pos ("Unclosed string"); Tokens.NSTSTRERR(pos,pos))
		end	
	else
		let 
			val pos = hd(!linePos);
			val error = ErrorMsg.error pos ("Comment not closed at end of file");
		in 
			Tokens.NSTCOMERR(pos,pos)
		end

(* Reverse the char list and join char into a string *)
fun makeString() = implode(rev(!current_string))

(* Add the escape char to the string list *)
fun appendChar(s) = current_string := s :: !current_string

(* ASCII char after 128 are not allowed *)
fun appendEscape(text, pos) =
	case Char.fromString(text) of 
		SOME(char) =>
			if Char.ord(char) < 128 then
		    	appendChar(char)
			else
			    ErrorMsg.error pos ("illegal ASCII escape " ^ text)
		| NONE => ErrorMsg.error pos ("illegal escape sequence " ^ text)

%% 
%s COMMENT STRING FEED;
alpha=[a-zA-Z];
digit=[0-9];
ws=[\ \t];
id=({alpha})({alpha}|{digit}|_)*;

%%
<INITIAL>"\""	=> (YYBEGIN STRING; current_string := []; nestedString := !nestedString + 1; string_start_pos := yypos; continue());
<STRING>"\""	=> (nestedString := !nestedString - 1; if !nestedString = 0 then (YYBEGIN INITIAL; Tokens.STRING(makeString(), !string_start_pos, yypos+1)) else continue());
<STRING>\\([nt\"\\]|[0-9]{3}|\^[@-_?])	=> (appendEscape(yytext,yypos); continue());
<STRING>\\(\^.|[^\t\r\f\n\ ])	=> (ErrorMsg.error yypos ("illegal escape character " ^ yytext); continue ());
<STRING>\\	=> (YYBEGIN FEED; continue());
<STRING>\n	=> (ErrorMsg.error yypos "illegal multiline string"; lineNum := !lineNum + 1; linePos := yypos :: !linePos; continue());
<STRING>.	=> (appendChar(String.sub(yytext, 0)); continue());

<FEED>\\	=> (YYBEGIN STRING; continue ());
<FEED>\n	=> (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<FEED>[\ \t\r]+	=> (continue());
<FEED>.	=> (YYBEGIN FEED; ErrorMsg.error yypos ("illegal feed character: " ^ yytext); continue ());

<INITIAL>"type" => (Tokens.TYPE(yypos, yypos + size(yytext)));
<INITIAL>"var" => (Tokens.VAR(yypos, yypos + size(yytext)));
<INITIAL>"function" => (Tokens.FUNCTION(yypos, yypos + size(yytext)));
<INITIAL>"break" => (Tokens.BREAK(yypos, yypos + size(yytext)));
<INITIAL>"of" => (Tokens.OF(yypos, yypos + size(yytext)));
<INITIAL>"end" => (Tokens.END(yypos, yypos + size(yytext)));
<INITIAL>"in" => (Tokens.IN(yypos, yypos + size(yytext)));
<INITIAL>"nil" => (Tokens.NIL(yypos, yypos + size(yytext)));
<INITIAL>"let" => (Tokens.LET(yypos, yypos + size(yytext)));
<INITIAL>"do" => (Tokens.DO(yypos, yypos + size(yytext)));
<INITIAL>"to" => (Tokens.TO(yypos, yypos + size(yytext)));
<INITIAL>"for" => (Tokens.FOR(yypos, yypos + size(yytext)));
<INITIAL>"while" => (Tokens.WHILE(yypos, yypos + size(yytext)));
<INITIAL>"else" => (Tokens.ELSE(yypos, yypos + size(yytext)));
<INITIAL>"then" => (Tokens.THEN(yypos, yypos + size(yytext)));
<INITIAL>"if" => (Tokens.IF(yypos, yypos + size(yytext)));
<INITIAL>"array" => (Tokens.ARRAY(yypos, yypos + size(yytext)));

<INITIAL>":=" => (Tokens.ASSIGN(yypos, yypos + size(yytext)));
<INITIAL>"|" => (Tokens.OR(yypos, yypos + size(yytext)));
<INITIAL>"&" => (Tokens.AND(yypos, yypos + size(yytext)));
<INITIAL>">=" => (Tokens.GE(yypos, yypos + size(yytext)));
<INITIAL>">" => (Tokens.GT(yypos, yypos + size(yytext)));
<INITIAL>"<=" => (Tokens.LE(yypos, yypos + size(yytext)));
<INITIAL>"<" => (Tokens.LT(yypos, yypos + size(yytext)));
<INITIAL>"<>" => (Tokens.NEQ(yypos, yypos + size(yytext)));
<INITIAL>"=" => (Tokens.EQ(yypos, yypos + size(yytext)));
<INITIAL>"/" => (Tokens.DIVIDE(yypos, yypos + size(yytext)));
<INITIAL>"*" => (Tokens.TIMES(yypos, yypos + size(yytext)));
<INITIAL>"-" => (Tokens.MINUS(yypos, yypos + size(yytext)));
<INITIAL>"+" => (Tokens.PLUS(yypos, yypos + size(yytext)));
<INITIAL>"." => (Tokens.DOT(yypos, yypos + size(yytext)));
<INITIAL>"}" => (Tokens.RBRACE(yypos, yypos + size(yytext)));
<INITIAL>"{" => (Tokens.LBRACE(yypos, yypos + size(yytext)));
<INITIAL>"]" => (Tokens.RBRACK(yypos, yypos + size(yytext)));
<INITIAL>"[" => (Tokens.LBRACK(yypos, yypos + size(yytext)));
<INITIAL>")" => (Tokens.RPAREN(yypos, yypos + size(yytext)));
<INITIAL>"(" => (Tokens.LPAREN(yypos, yypos + size(yytext)));
<INITIAL>";" => (Tokens.SEMICOLON(yypos, yypos + size(yytext)));
<INITIAL>":" => (Tokens.COLON(yypos, yypos + size(yytext)));
<INITIAL>"," => (Tokens.COMMA(yypos, yypos + size(yytext)));

<INITIAL>{digit}+ =>(Tokens.INT(valOf(Int.fromString(yytext)), yypos, yypos + size(yytext)));
<INITIAL>{id} => (Tokens.ID(yytext, yypos, yypos + size(yytext)));
<INITIAL>{ws}+ => (continue());
<INITIAL>\n	=> (lineNum := !lineNum + 1; linePos := yypos :: !linePos; continue());

<INITIAL>"/*" => (YYBEGIN COMMENT; nestedComment := 1; continue());
<COMMENT>"/*" => (nestedComment := !nestedComment + 1; continue());
<COMMENT>"*/" => (nestedComment := !nestedComment - 1; if (!nestedComment = 0) then (YYBEGIN INITIAL; continue()) else continue());  
<COMMENT>\n => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<COMMENT>. => (continue());

.       => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());