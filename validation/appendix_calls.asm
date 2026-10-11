.686
.model flat, C
option casemap:none
.code
PUBLIC AppendixBracket, AppendixBracketEnd, AppendixDirect, AppendixDirectEnd
PUBLIC AppendixIndirect, AppendixIndirectEnd
AppendixCalls PROC
AppendixBracket::
    call [AppendixBracket+1+4]
AppendixBracketEnd::
    ret
AppendixDirect::
    call AppendixDirectEnd
AppendixDirectEnd::
    ret
AppendixIndirect::
    call dword ptr [AppendixIndirect+1+4]
AppendixIndirectEnd::
    ret
AppendixCalls ENDP
END
