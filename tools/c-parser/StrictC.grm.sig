signature StrictC_TOKENS =
sig
type ('a,'b) token
type svalue
val YREGISTER:  'a * 'a -> (svalue,'a) token
val YASM:  'a * 'a -> (svalue,'a) token
val GCC_ATTRIBUTE:  'a * 'a -> (svalue,'a) token
val SPEC_BLOCKEND:  'a * 'a -> (svalue,'a) token
val STRING_LITERAL: (string) *  'a * 'a -> (svalue,'a) token
val DONT_TRANSLATE:  'a * 'a -> (svalue,'a) token
val SPEC_END:  'a * 'a -> (svalue,'a) token
val SPEC_BEGIN:  'a * 'a -> (svalue,'a) token
val OWNED_BY:  'a * 'a -> (svalue,'a) token
val CALLS:  'a * 'a -> (svalue,'a) token
val MODIFIES:  'a * 'a -> (svalue,'a) token
val GHOSTUPD:  'a * 'a -> (svalue,'a) token
val AUXUPD:  'a * 'a -> (svalue,'a) token
val RELSPEC:  'a * 'a -> (svalue,'a) token
val FNSPEC:  'a * 'a -> (svalue,'a) token
val AUTO:  'a * 'a -> (svalue,'a) token
val THREAD_LOCAL:  'a * 'a -> (svalue,'a) token
val NORETURN:  'a * 'a -> (svalue,'a) token
val STATIC:  'a * 'a -> (svalue,'a) token
val INLINE:  'a * 'a -> (svalue,'a) token
val INVARIANT:  'a * 'a -> (svalue,'a) token
val RESTRICT:  'a * 'a -> (svalue,'a) token
val VOLATILE:  'a * 'a -> (svalue,'a) token
val CONST:  'a * 'a -> (svalue,'a) token
val EXTERN:  'a * 'a -> (svalue,'a) token
val TYPEDEF:  'a * 'a -> (svalue,'a) token
val UNION:  'a * 'a -> (svalue,'a) token
val STRUCT:  'a * 'a -> (svalue,'a) token
val NUMERIC_CONSTANT: (Absyn.numliteral_info) *  'a * 'a -> (svalue,'a) token
val TYPEID: (string) *  'a * 'a -> (svalue,'a) token
val ID: (string) *  'a * 'a -> (svalue,'a) token
val ARROW:  'a * 'a -> (svalue,'a) token
val VOID:  'a * 'a -> (svalue,'a) token
val UNSIGNED:  'a * 'a -> (svalue,'a) token
val SIGNED:  'a * 'a -> (svalue,'a) token
val SHORT:  'a * 'a -> (svalue,'a) token
val LONG:  'a * 'a -> (svalue,'a) token
val CHAR:  'a * 'a -> (svalue,'a) token
val BOOL:  'a * 'a -> (svalue,'a) token
val INT:  'a * 'a -> (svalue,'a) token
val RIGHTSHIFT:  'a * 'a -> (svalue,'a) token
val LEFTSHIFT:  'a * 'a -> (svalue,'a) token
val YGREATER:  'a * 'a -> (svalue,'a) token
val YLESS:  'a * 'a -> (svalue,'a) token
val YGE:  'a * 'a -> (svalue,'a) token
val YLE:  'a * 'a -> (svalue,'a) token
val NOTEQUALS:  'a * 'a -> (svalue,'a) token
val EQUALS:  'a * 'a -> (svalue,'a) token
val BITWISEXOR:  'a * 'a -> (svalue,'a) token
val BITWISEOR:  'a * 'a -> (svalue,'a) token
val LOGICALAND:  'a * 'a -> (svalue,'a) token
val LOGICALOR:  'a * 'a -> (svalue,'a) token
val YSIZEOF:  'a * 'a -> (svalue,'a) token
val DEFAULT:  'a * 'a -> (svalue,'a) token
val CASE:  'a * 'a -> (svalue,'a) token
val SWITCH:  'a * 'a -> (svalue,'a) token
val YFOR:  'a * 'a -> (svalue,'a) token
val YCONTINUE:  'a * 'a -> (svalue,'a) token
val YBREAK:  'a * 'a -> (svalue,'a) token
val YRETURN:  'a * 'a -> (svalue,'a) token
val YDO:  'a * 'a -> (svalue,'a) token
val YWHILE:  'a * 'a -> (svalue,'a) token
val YELSE:  'a * 'a -> (svalue,'a) token
val YIF:  'a * 'a -> (svalue,'a) token
val YENUM:  'a * 'a -> (svalue,'a) token
val RSHIFTEQ:  'a * 'a -> (svalue,'a) token
val LSHIFTEQ:  'a * 'a -> (svalue,'a) token
val BXOREQ:  'a * 'a -> (svalue,'a) token
val MODEQ:  'a * 'a -> (svalue,'a) token
val DIVEQ:  'a * 'a -> (svalue,'a) token
val MULEQ:  'a * 'a -> (svalue,'a) token
val BOREQ:  'a * 'a -> (svalue,'a) token
val BANDEQ:  'a * 'a -> (svalue,'a) token
val MINUSEQ:  'a * 'a -> (svalue,'a) token
val PLUSEQ:  'a * 'a -> (svalue,'a) token
val MINUSMINUS:  'a * 'a -> (svalue,'a) token
val PLUSPLUS:  'a * 'a -> (svalue,'a) token
val YBITNOT:  'a * 'a -> (svalue,'a) token
val YAMPERSAND:  'a * 'a -> (svalue,'a) token
val YNOT:  'a * 'a -> (svalue,'a) token
val YAND:  'a * 'a -> (svalue,'a) token
val YMINUS:  'a * 'a -> (svalue,'a) token
val YPLUS:  'a * 'a -> (svalue,'a) token
val YDOT:  'a * 'a -> (svalue,'a) token
val YEQ:  'a * 'a -> (svalue,'a) token
val QMARK:  'a * 'a -> (svalue,'a) token
val YCOLON:  'a * 'a -> (svalue,'a) token
val YSEMI:  'a * 'a -> (svalue,'a) token
val YCOMMA:  'a * 'a -> (svalue,'a) token
val RBRACKET:  'a * 'a -> (svalue,'a) token
val LBRACKET:  'a * 'a -> (svalue,'a) token
val RCURLY:  'a * 'a -> (svalue,'a) token
val LCURLY:  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val MOD:  'a * 'a -> (svalue,'a) token
val SLASH:  'a * 'a -> (svalue,'a) token
val YSTAR:  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
end
signature StrictC_LRVALS=
sig
structure Tokens : StrictC_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
