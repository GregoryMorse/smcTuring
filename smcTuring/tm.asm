ifndef X64
.model flat, C
endif
option casemap :none

.code

ifndef X64
ADDRPLIER EQU 4
SIZEWORD TEXTEQU <dword>

X TEXTEQU <eax>
Y TEXTEQU <ebx>
M TEXTEQU <ecx>
Z EQU Y
D EQU Z
H EQU M
L TEXTEQU <edi>
R EQU L
T EQU R
S TEXTEQU <edx>
N TEXTEQU <esi>

;eax, ecx, edx are considered volatile
MovTM PROC USES ebx edi esi TransitionTapePtr: DWORD, InputTape: DWORD, InputTapeLeft: DWORD, scratch: DWORD, InputTapePtr: DWORD, InputTapeLeftPtr: DWORD
else
ADDRPLIER EQU 8
SIZEWORD TEXTEQU <qword>

X TEXTEQU <rax>
Y TEXTEQU <rbx>
M TEXTEQU <rdi>
Z EQU Y
D EQU Z
H EQU M
L TEXTEQU <r10>
R EQU L
T TEXTEQU <rcx>
S TEXTEQU <rdx>
N TEXTEQU <r8>
scratch TEXTEQU <r9>
TransitionTapePtr TextEQU <T>
InputTape TextEQU <S>
InputTapeLeft TextEQU <N>

;rax, rcx, rdx, r8, r9, r10, r11 are considered volatile
;x64 calling convention passes arguments fastcall: RCX, RDX, R8, R9, on stack but using default argument scheme uses stack and without first 4 indexes them incorrectly
;PROC -> DWORD PTR[rsp + 40] also could work here to use a more appropriate esp based indexing instead of ebp

MovTM PROC USES rbx rdi Dummy1: QWORD, Dummy2: QWORD, Dummy3: QWORD, Dummy4: QWORD, InputTapePtr: QWORD, InputTapeLeftPtr: QWORD
endif
		mov T, TransitionTapePtr;; current state, initially Q0
		mov S, InputTape;; current symbol, initially Q0
		mov N, InputTapeLeft;; scratch part of tape left of current position, initially empty

	start:
		mov X, [T];; get transition
		mov X, [X];; get trigger symbol
		mov Y, [S];; get current symbol
		mov SIZEWORD ptr [scratch + Y * ADDRPLIER], 0;; compare symbols
		mov SIZEWORD ptr [scratch + X * ADDRPLIER], 1 * ADDRPLIER
		mov M, SIZEWORD ptr [scratch + Y * ADDRPLIER]

		mov X, [T];; get transition
		mov X, [X + 1 * ADDRPLIER];; skip trigger symbol
		mov X, [X];; load new symbol
		mov Y, [S];; load old symbol
		mov [N], Y;; select between X and Y
		mov [N + 1 * ADDRPLIER], X
		mov Z, [N + M]
		mov [S], Z;; write the new symbol

		mov D, [T];; get transition
		mov D, [D + 1 * ADDRPLIER];; skip trigger symbol
		mov D, [D + 1 * ADDRPLIER];; skip new symbol
		mov D, [D];; load direction

			mov R, InputTapePtr
		mov [N], R;; select new value for[S + 1]
			mov L, InputTapeLeftPtr
		mov [N + 1 * ADDRPLIER], L
		mov X, [N + D]
		mov [S + 1 * ADDRPLIER], X
		mov [N], L;; select new value for L
		mov [N + 1 * ADDRPLIER], S
		mov L, [N + D]
			mov InputTapeLeftPtr, L
		mov [N], S;; select new value for R
			mov R, InputTapePtr
		mov [N + 1 * ADDRPLIER], R
		mov R, [N + D]
			mov InputTapePtr, R

		mov SIZEWORD ptr [N], 1 * ADDRPLIER;; set X = not D
		mov SIZEWORD ptr [N + 1 * ADDRPLIER], 0
		mov X, [N + D]
		mov [N], X;; select between D and X
		mov [N + 1 * ADDRPLIER], D
		mov D, [N + M]

			mov L, InputTapeLeftPtr
		mov [N], L;; select new value of S
			mov R, InputTapePtr
		mov [N + 1 * ADDRPLIER], R
		mov S, [N + D]
		mov X, [S + 1 * ADDRPLIER];; get new start of L or R
		mov [N], X;; select new value for L
			mov L, InputTapeLeftPtr
		mov [N + 1 * ADDRPLIER], L
		mov L, [N + D]
			mov InputTapeLeftPtr, L
			mov R, InputTapePtr
		mov [N], R;; select new value for R
		mov [N + 1 * ADDRPLIER], X
		mov R, [N + D]
			mov InputTapePtr, R

			mov T, TransitionTapePtr
		mov X, [T + 1 * ADDRPLIER];; get next transition of this state
		mov Y, [T];; get current transition
		mov Y, [Y + 1 * ADDRPLIER];; skip trigger symbol
		mov Y, [Y + 1 * ADDRPLIER];; skip new symbol
		mov Y, [Y + 1 * ADDRPLIER];; skip direction
		mov Y, [Y];; load transition list of next state
		mov [N], X;; select next transition
		mov [N + 1 * ADDRPLIER], Y
		mov T, [N + M]
			mov TransitionTapePtr, T

		mov X, [T]
		mov SIZEWORD ptr [N], 1 * ADDRPLIER
		mov SIZEWORD ptr [T], 0
		mov H, [N]
		mov [T], X

		mov SIZEWORD ptr [N], 0;; select between 0 and N
		mov [N + 1 * ADDRPLIER], N
		mov X, [N + H]
			cmp X, 0
			je finish
		mov X, [X];; load from 0 or N
		jmp start
	finish:
		ret
MovTM ENDP

ifndef X64
ACCUMULATOR TEXTEQU <eax>
COUNTER TEXTEQU <ecx>
AsmTM PROC TransitionTape: DWORD, InputTape: DWORD, CurTransitionPtr: DWORD, CurInputPtr: DWORD, CurState: BYTE
else
ACCUMULATOR TEXTEQU <rax>
COUNTER TEXTEQU <r10>
TransitionTape TEXTEQU <rcx>
InputTape TEXTEQU <rdx>
CurTransitionPtr TEXTEQU <r8>
CurInputPtr TEXTEQU <r9>
AsmTM PROC Dummy1: QWORD, Dummy2: QWORD, Dummy3: QWORD, Dummy4: QWORD, CurState: BYTE
endif

		mov ACCUMULATOR, TransitionTape
		mov CurTransitionPtr, ACCUMULATOR
		mov ACCUMULATOR, InputTape
		mov CurInputPtr, ACCUMULATOR
	begin:
		mov ACCUMULATOR, CurTransitionPtr
		mov al, byte ptr [ACCUMULATOR]
		cmp al, CurState
		jne next

		mov ACCUMULATOR, CurTransitionPtr
		mov al, byte ptr [ACCUMULATOR + 1]
		mov COUNTER, CurInputPtr
		cmp al, byte ptr [COUNTER]
		jne next

		mov ACCUMULATOR, CurTransitionPtr
		mov al, byte ptr [ACCUMULATOR + 4]
		mov CurState, al

		mov ACCUMULATOR, CurTransitionPtr
		mov al, byte ptr [ACCUMULATOR + 2]
		mov COUNTER, CurInputPtr
		mov byte ptr [COUNTER], al

		mov ACCUMULATOR, CurTransitionPtr
		movsx ACCUMULATOR, byte ptr [ACCUMULATOR + 3]
		add CurInputPtr, ACCUMULATOR

		cmp CurState, '2'
		je success

		mov ACCUMULATOR, TransitionTape
		mov CurTransitionPtr, ACCUMULATOR

		jmp begin
	next:
		add CurTransitionPtr, 5
		mov ACCUMULATOR, InputTape
		cmp CurTransitionPtr, ACCUMULATOR
		je fail
		jmp begin
	fail:
	success:
		ret
AsmTM ENDP

ifndef X64
AsmListTM PROC TransitionTape: DWORD, InputTape: DWORD, CurTransitionPtr: DWORD, CurInputPtr: DWORD, CurState: BYTE
else
AsmListTM PROC
endif
	mov ACCUMULATOR, TransitionTape
	mov CurTransitionPtr, ACCUMULATOR
	mov ACCUMULATOR, InputTape
	mov CurInputPtr, ACCUMULATOR
	dobegin:
		mov ACCUMULATOR, CurTransitionPtr
		mov ACCUMULATOR, SIZEWORD ptr[ACCUMULATOR + 1 * ADDRPLIER]
		mov COUNTER, CurInputPtr
		cmp al, byte ptr[COUNTER]
		jne donext

		mov ACCUMULATOR, CurTransitionPtr
		mov ACCUMULATOR, SIZEWORD ptr[ACCUMULATOR + 2 * ADDRPLIER]
		mov COUNTER, CurInputPtr
		mov byte ptr[COUNTER], al

		mov ACCUMULATOR, CurTransitionPtr
		movsx ACCUMULATOR, byte ptr[ACCUMULATOR + 3 * ADDRPLIER]
		add CurInputPtr, ACCUMULATOR

		mov ACCUMULATOR, CurTransitionPtr
		mov ACCUMULATOR, SIZEWORD ptr[ACCUMULATOR + 4 * ADDRPLIER]
		mov CurTransitionPtr, ACCUMULATOR
		jmp check
	donext:
		mov ACCUMULATOR, CurTransitionPtr
		mov ACCUMULATOR, SIZEWORD ptr[ACCUMULATOR]
		mov CurTransitionPtr, ACCUMULATOR
	check:
		cmp CurTransitionPtr, 0
		je finishlist
		jmp dobegin
	finishlist:
		ret
AsmListTM ENDP

END