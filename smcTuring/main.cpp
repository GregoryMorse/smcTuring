//Gregory Morse
//implementation of Stephen Dolan's mov is Turing-complete research paper: https://www.cl.cam.ac.uk/~sd601/papers/mov.pdf

#include <iostream>
#include <basetsd.h>
#include <Windows.h>

extern "C" void __cdecl MovTM(ULONG_PTR, ULONG_PTR, ULONG_PTR, ULONG_PTR, ULONG_PTR, ULONG_PTR);
extern "C" void __cdecl AsmTM(ULONG_PTR, ULONG_PTR, ULONG_PTR, ULONG_PTR, unsigned char);
extern "C" void __cdecl AsmListTM(ULONG_PTR, ULONG_PTR, ULONG_PTR, ULONG_PTR);

//mov being Turing complete
//3 instructions needed:
//Load Immediate mov Rdest, c
//Load Indexed mov Rdest, [Rsrc + Roffset]
//Store Indexed mov[Rdest + Roffset], Rsrc

int TMCmp(const void* l, const void* r)
{
	if (*(unsigned char*)l == *(unsigned char*)r) return 0;
	return *(unsigned char*)l > *(unsigned char*)r ? 1 : -1;
}

void MovTM(char turingMachine[][5], int tmSize, char* Input, int inpSize, bool bOutput, int InExAsmC)
{
	//<pointer to trigger symbol> <pointer to next state> <trigger symbol> <pointer to new symbol> <new symbol> <pointer to direction> <direction> <pointer to pointer to new state> <pointer to new state>
	ULONG_PTR* TransitionTape = (ULONG_PTR*)malloc((tmSize / 5) * 9 * sizeof(ULONG_PTR)); //{old state, old symbol, new symbol, direction, new state}
	ULONG_PTR* InputTape = (ULONG_PTR*)malloc(inpSize * sizeof(ULONG_PTR) * 2);
	ULONG_PTR* InputTapeLeft = (ULONG_PTR*)malloc(inpSize * sizeof(ULONG_PTR) * 2);
	for (int i = 0; i < tmSize / 5; i++) {
		TransitionTape[i * 9] = (ULONG_PTR)(TransitionTape + i * 9) + sizeof(ULONG_PTR) * 2;
		TransitionTape[i * 9 + 3] = (ULONG_PTR)(TransitionTape + i * 9) + sizeof(ULONG_PTR) * 4;
		TransitionTape[i * 9 + 5] = (ULONG_PTR)(TransitionTape + i * 9) + sizeof(ULONG_PTR) * 6;
		TransitionTape[i * 9 + 7] = (ULONG_PTR)(TransitionTape + i * 9) + sizeof(ULONG_PTR) * 8;
		char* ptr = (char*)bsearch(&turingMachine[i][4], turingMachine, tmSize / 5, 5, TMCmp);
		LONG_PTR idx;
		if (ptr != NULL) {
			idx = (ptr - (char*)turingMachine) / 5;
			while (idx != 0 && turingMachine[idx - 1][0] == turingMachine[i][4]) idx--;
		}
		TransitionTape[i * 9 + 8] = ptr == NULL ? (turingMachine[i][4] == '2' ? (ULONG_PTR)InputTapeLeft : (ULONG_PTR)InputTapeLeft) : (ULONG_PTR)(TransitionTape + (idx * 9));
		TransitionTape[i * 9 + 2] = turingMachine[i][1];
		TransitionTape[i * 9 + 4] = turingMachine[i][2];
		TransitionTape[i * 9 + 6] = turingMachine[i][3] == 'R' ? sizeof(ULONG_PTR) : 0;
		TransitionTape[i * 9 + 1] = ((i == tmSize / 5 - 1) || turingMachine[i + 1][0] != turingMachine[i][0]) ? (ULONG_PTR)InputTapeLeft : (ULONG_PTR)(TransitionTape + (i + 1) * 9);
	}
	for (int i = 0; i < inpSize; i++) {
		InputTape[i * 2] = Input[i];
		InputTapeLeft[i * 2] = '_';
		InputTape[i * 2 + 1] = (ULONG_PTR)(InputTape + (i + 1) * 2);
		InputTapeLeft[i * 2 + 1] = (ULONG_PTR)(InputTapeLeft + (i + 1) * 2);
	}
	ULONG_PTR scratch[256]; // must be the size of the alphabet range
	ULONG_PTR TransitionTapePtr = (ULONG_PTR)TransitionTape;
	ULONG_PTR InputTapePtr = (ULONG_PTR)InputTape + sizeof(ULONG_PTR) * 2; //part of tape right of current position, initially at beginning of input tape after current symbol
	ULONG_PTR InputTapeLeftPtr = (ULONG_PTR)InputTapeLeft; //part of tape left of current position, initially empty
	if (InExAsmC & 2)
		MovTM((ULONG_PTR)TransitionTapePtr, (ULONG_PTR)InputTape, (ULONG_PTR)InputTapeLeft, (ULONG_PTR)scratch, (ULONG_PTR)InputTapePtr, (ULONG_PTR)InputTapeLeftPtr);
	if (bOutput) {
		printf("External assembly mov Turing machine: %s -> ", Input);
		for (int i = 0; i < inpSize; i++) printf("%c", (char)InputTape[i * 2]);
		printf("\n");
	}
#if !defined(_WIN64)
	if (InExAsmC & 1) {
		for (int i = 0; i < inpSize; i++) {
			InputTape[i * 2] = Input[i];
			InputTapeLeft[i * 2] = '_';
			InputTape[i * 2 + 1] = (ULONG_PTR)(InputTape + (i + 1) * 2);
			InputTapeLeft[i * 2 + 1] = (ULONG_PTR)(InputTapeLeft + (i + 1) * 2);
		}
#define ADDRPLIER 4
#define SIZEWORD dword
		//temporary registers, 4 of which are mutually exclusive in usage
#define X eax
#define Y ebx
#define M ecx
#define Z Y
#define D Z
#define H M
	//5 globally used registers
#define L edi
#define R L
#define T R
#define S edx
#define N esi

		__asm {
			mov T, TransitionTapePtr;; current state, initially Q0
			mov S, InputTape;; current symbol, initially Q0
			mov N, InputTapeLeft;; scratch part of tape left of current position, initially empty

			start:
				mov X, [T];; get transition
				mov X, [X];; get trigger symbol
				mov Y, [S];; get current symbol
				mov SIZEWORD ptr[scratch + Y * ADDRPLIER], 0;; compare symbols
				mov SIZEWORD ptr[scratch + X * ADDRPLIER], 1 * 4
				mov M, SIZEWORD ptr[scratch + Y * ADDRPLIER]

				mov X, [T];; get transition
				mov X, [X + 1 * ADDRPLIER];; skip trigger symbol
				mov X, [X];; load new symbol
				mov Y, [S];; load old symbol
				mov[N], Y;; select between X and Y
				mov[N + 1 * ADDRPLIER], X
				mov Z, [N + M]
				mov[S], Z;; write the new symbol

				mov D, [T];; get transition
				mov D, [D + 1 * ADDRPLIER];; skip trigger symbol
				mov D, [D + 1 * ADDRPLIER];; skip new symbol
				mov D, [D];; load direction

				mov R, InputTapePtr
				mov[N], R;; select new value for[S + 1]
				mov L, InputTapeLeftPtr
				mov[N + 1 * ADDRPLIER], L
				mov X, [N + D]
				mov[S + 1 * ADDRPLIER], X
				mov[N], L;; select new value for L
				mov[N + 1 * ADDRPLIER], S
				mov L, [N + D]
				mov InputTapeLeftPtr, L
				mov[N], S;; select new value for R
				mov R, InputTapePtr
				mov[N + 1 * ADDRPLIER], R
				mov R, [N + D]
				mov InputTapePtr, R

				mov SIZEWORD ptr[N], 1 * ADDRPLIER;; set X = not D
				mov SIZEWORD ptr[N + 1 * ADDRPLIER], 0
				mov X, [N + D]
				mov[N], X;; select between D and X
				mov[N + 1 * ADDRPLIER], D
				mov D, [N + M]

				mov L, InputTapeLeftPtr
				mov[N], L;; select new value of S
				mov R, InputTapePtr
				mov[N + 1 * ADDRPLIER], R
				mov S, [N + D]
				mov X, [S + 1 * ADDRPLIER];; get new start of L or R
				mov[N], X;; select new value for L
				mov L, InputTapeLeftPtr
				mov[N + 1 * ADDRPLIER], L
				mov L, [N + D]
				mov InputTapeLeftPtr, L
				mov R, InputTapePtr
				mov[N], R;; select new value for R
				mov[N + 1 * ADDRPLIER], X
				mov R, [N + D]
				mov InputTapePtr, R

				mov T, TransitionTapePtr
				mov X, [T + 1 * ADDRPLIER];; get next transition of this state
				mov Y, [T];; get current transition
				mov Y, [Y + 1 * ADDRPLIER];; skip trigger symbol
				mov Y, [Y + 1 * ADDRPLIER];; skip new symbol
				mov Y, [Y + 1 * ADDRPLIER];; skip direction
				mov Y, [Y];; load transition list of next state
				mov[N], X;; select next transition
				mov[N + 1 * ADDRPLIER], Y
				mov T, [N + M]
				mov TransitionTapePtr, T

				mov X, [T]
				mov SIZEWORD ptr[N], 1 * ADDRPLIER
				mov SIZEWORD ptr[T], 0
				mov H, [N]
				mov[T], X

				mov SIZEWORD ptr[N], 0;; select between 0 and N
				mov[N + 1 * ADDRPLIER], N
				mov X, [N + H]
				cmp X, 0
				je finish
				mov X, [X];; load from 0 or N
				jmp start
			finish:
		}
		if (bOutput) {
			printf("Inline assembly mov Turing machine: %s -> ", Input);
			for (int i = 0; i < inpSize; i++) printf("%c", InputTape[i * 2]);
			printf("\n");
		}
	}
#endif
	if (InExAsmC & 4) {
		for (int i = 0; i < inpSize; i++) {
			InputTape[i * 2] = Input[i];
			InputTapeLeft[i * 2] = '_';
			InputTape[i * 2 + 1] = (ULONG_PTR)(InputTape + (i + 1) * 2);
			InputTapeLeft[i * 2 + 1] = (ULONG_PTR)(InputTapeLeft + (i + 1) * 2);
		}
		ULONG_PTR CurInputTapePtr = (ULONG_PTR)InputTape;
		TransitionTapePtr = (ULONG_PTR)TransitionTape;
		InputTapePtr = (ULONG_PTR)InputTape + sizeof(ULONG_PTR) * 2;
		InputTapeLeftPtr = (ULONG_PTR)InputTapeLeft;
		do {
			if (*(ULONG_PTR*)(*(ULONG_PTR*)TransitionTapePtr) == *(ULONG_PTR*)CurInputTapePtr) {
				*(ULONG_PTR*)CurInputTapePtr = *(ULONG_PTR*)(*(ULONG_PTR*)(*(ULONG_PTR*)TransitionTapePtr + sizeof(ULONG_PTR)));
				if (*(ULONG_PTR*)(*(ULONG_PTR*)(*(ULONG_PTR*)(*(ULONG_PTR*)TransitionTapePtr + sizeof(ULONG_PTR)) + sizeof(ULONG_PTR))) == 0) {
					*(ULONG_PTR*)(CurInputTapePtr + sizeof(ULONG_PTR)) = InputTapePtr;
					InputTapePtr = CurInputTapePtr;
					CurInputTapePtr = InputTapeLeftPtr;
					InputTapeLeftPtr = *(ULONG_PTR*)(CurInputTapePtr + sizeof(ULONG_PTR));
				}
				else {
					*(ULONG_PTR*)(CurInputTapePtr + sizeof(ULONG_PTR)) = InputTapeLeftPtr;
					InputTapeLeftPtr = CurInputTapePtr;
					CurInputTapePtr = InputTapePtr;
					InputTapePtr = *(ULONG_PTR*)(CurInputTapePtr + sizeof(ULONG_PTR));
				}
				TransitionTapePtr = *(ULONG_PTR*)(*(ULONG_PTR*)(*(ULONG_PTR*)(*(ULONG_PTR*)(*(ULONG_PTR*)TransitionTapePtr + sizeof(ULONG_PTR)) + sizeof(ULONG_PTR)) + sizeof(ULONG_PTR)));
			}
			else {
				TransitionTapePtr = *(ULONG_PTR*)(TransitionTapePtr + sizeof(ULONG_PTR));
			}
		} while (TransitionTapePtr != (ULONG_PTR)InputTapeLeft);
		if (bOutput) {
			printf("C mov Turing machine: %s -> ", Input);
			for (int i = 0; i < inpSize; i++) printf("%c", (char)InputTape[i * 2]);
			printf("\n");
		}
	}

	free(TransitionTape);
	free(InputTape);
	free(InputTapeLeft);
}

void CTM(char turingMachine[][5], int tmSize, char* Input, int inpSize, bool bOutput, int LimUnlim)
{
	//not general example: limited transition state capacity, one sided tape
	unsigned char* TransitionTape = (unsigned char*)malloc(tmSize + inpSize);//{old state, old symbol, new symbol, direction, new state}
	memcpy(TransitionTape, turingMachine, tmSize);
	for (int i = 0; i < tmSize / 5; i++) { TransitionTape[i * 5 + 3] = TransitionTape[i * 5 + 3] == 'R' ? 1 : -1; }
	unsigned char* InputTape = TransitionTape + tmSize;
	memcpy(InputTape, Input, inpSize);
	unsigned char* CurInputPtr = InputTape;
	unsigned char* CurTransitionPtr = TransitionTape;
	unsigned char CurState = '1';
	if (LimUnlim & 1) {
		do {
			if (CurTransitionPtr[0] == CurState && CurTransitionPtr[1] == *CurInputPtr) {
				CurState = CurTransitionPtr[4];
				*CurInputPtr = CurTransitionPtr[2];
				CurInputPtr += (char)CurTransitionPtr[3];
				if (CurState == '2') break;
				CurTransitionPtr = TransitionTape;
			}
			else {
				CurTransitionPtr += 5;
			}
		} while (CurTransitionPtr != InputTape);
		if (bOutput) {
			printf("C Turing machine limited transitions: %s -> ", Input);
			fwrite(InputTape, 1, inpSize, stdout);
			printf("\n");
		}
	}
	free(TransitionTape);

	if (LimUnlim & 2) {
		//general example with unlimited transition state capacity, dual sided tape
		ULONG_PTR* TransitionTape = (ULONG_PTR*)malloc(sizeof(ULONG_PTR) * tmSize);
		for (int i = 0; i < tmSize / 5; i++) {
			TransitionTape[i * 5] = ((i == tmSize / 5 - 1) || turingMachine[i + 1][0] != turingMachine[i][0]) ? NULL : (ULONG_PTR)(TransitionTape + (i + 1) * 5);
			TransitionTape[i * 5 + 1] = turingMachine[i][1];
			TransitionTape[i * 5 + 2] = turingMachine[i][2];
			TransitionTape[i * 5 + 3] = turingMachine[i][3] == 'R' ? 1 : -1;
			char* ptr = (char*)bsearch(&turingMachine[i][4], turingMachine, tmSize / 5, 5, TMCmp);
			LONG_PTR idx;
			if (ptr != NULL) {
				idx = (ptr - (char*)turingMachine) / 5;
				while (idx != 0 && turingMachine[idx - 1][0] == turingMachine[i][4]) idx--;
			}
			TransitionTape[i * 5 + 4] = ptr == NULL ? (turingMachine[i][4] == '2' ? NULL : NULL) : (ULONG_PTR)(TransitionTape + (idx * 5));
		}
		unsigned char* InputTape = (unsigned char*)malloc(inpSize);
		memcpy(InputTape, Input, inpSize);
		unsigned char* CurInputPtr = InputTape;
		ULONG_PTR* CurTransitionPtr = TransitionTape;
		do {
			if (CurTransitionPtr[1] == *CurInputPtr) {
				*CurInputPtr = (char)CurTransitionPtr[2];
				CurInputPtr += (char)CurTransitionPtr[3];
				CurTransitionPtr = (ULONG_PTR*)CurTransitionPtr[4];
			}
			else {
				CurTransitionPtr = (ULONG_PTR*)CurTransitionPtr[0];
			}
		} while (CurTransitionPtr != NULL);
		if (bOutput) {
			printf("C Turing machine: %s -> ", Input);
			fwrite(InputTape, 1, inpSize, stdout);
			printf("\n");
		}
		free(TransitionTape);
		free(InputTape);
	}
}

void AsmTM(char turingMachine[][5], int tmSize, char* Input, int inpSize, bool bOutput, int InExLimUnlim)
{
	//not general example: limited transition state capacity, one sided tape
	unsigned char* TransitionTape = (unsigned char*)malloc(tmSize + inpSize);//{old state, old symbol, new symbol, direction, new state}
	memcpy(TransitionTape, turingMachine, tmSize);
	for (int i = 0; i < tmSize / 5; i++) { TransitionTape[i * 5 + 3] = TransitionTape[i * 5 + 3] == 'R' ? 1 : -1; }
	unsigned char* InputTape = TransitionTape + tmSize;
	memcpy(InputTape, Input, inpSize);
	unsigned char CurState = '1';
	unsigned long CurInputPtr;
	unsigned long CurTransitionPtr;
	if (InExLimUnlim & 2)
		AsmTM((ULONG_PTR)TransitionTape, (ULONG_PTR)InputTape, (ULONG_PTR)&CurTransitionPtr, (ULONG_PTR)&CurInputPtr, CurState);
	if (bOutput) {
		printf("External assembly Turing machine limited transitions: %s -> ", Input);
		fwrite(InputTape, 1, inpSize, stdout);
		printf("\n");
	}
#if !defined(_WIN64)
#define ACCUMULATOR eax
#define COUNTER ecx
	if (InExLimUnlim & 1) {
		memcpy(InputTape, Input, inpSize);
		__asm {
			mov ACCUMULATOR, TransitionTape
			mov CurTransitionPtr, ACCUMULATOR
			mov ACCUMULATOR, InputTape
			mov CurInputPtr, ACCUMULATOR
			begin :
			mov ACCUMULATOR, CurTransitionPtr
				mov al, byte ptr[ACCUMULATOR]
				cmp al, CurState
				jne next

				mov ACCUMULATOR, CurTransitionPtr
				mov al, byte ptr[ACCUMULATOR + 1]
				mov COUNTER, CurInputPtr
				cmp al, byte ptr[COUNTER]
				jne next

				mov ACCUMULATOR, CurTransitionPtr
				mov al, byte ptr[ACCUMULATOR + 4]
				mov CurState, al

				mov ACCUMULATOR, CurTransitionPtr
				mov al, byte ptr[ACCUMULATOR + 2]
				mov COUNTER, CurInputPtr
				mov byte ptr[COUNTER], al

				mov ACCUMULATOR, CurTransitionPtr
				movsx ACCUMULATOR, byte ptr[ACCUMULATOR + 3]
				add CurInputPtr, ACCUMULATOR

				cmp CurState, '2'
				je success

				mov ACCUMULATOR, TransitionTape
				mov CurTransitionPtr, ACCUMULATOR

				jmp begin
				next :
			add CurTransitionPtr, 5
				mov ACCUMULATOR, InputTape
				cmp CurTransitionPtr, ACCUMULATOR
				je fail
				jmp begin
			fail:
			success:
		}
		if (bOutput) {
			printf("Inline assembly Turing machine limited transitions: %s -> ", Input);
			fwrite(InputTape, 1, inpSize, stdout);
			printf("\n");
		}
	}
#endif
	free(TransitionTape);

	if (InExLimUnlim & (4 | 8)) {
		//general example with unlimited transition state capacity, dual sided tape
		ULONG_PTR* TransitionTape = (ULONG_PTR*)malloc(sizeof(ULONG_PTR) * tmSize);
		for (int i = 0; i < tmSize / 5; i++) {
			TransitionTape[i * 5] = ((i == tmSize / 5 - 1) || turingMachine[i + 1][0] != turingMachine[i][0]) ? NULL : (ULONG_PTR)(TransitionTape + (i + 1) * 5);
			TransitionTape[i * 5 + 1] = turingMachine[i][1];
			TransitionTape[i * 5 + 2] = turingMachine[i][2];
			TransitionTape[i * 5 + 3] = turingMachine[i][3] == 'R' ? 1 : -1;
			char* ptr = (char*)bsearch(&turingMachine[i][4], turingMachine, tmSize / 5, 5, TMCmp);
			LONG_PTR idx;
			if (ptr != NULL) {
				idx = (ptr - (char*)turingMachine) / 5;
				while (idx != 0 && turingMachine[idx - 1][0] == turingMachine[i][4]) idx--;
			}
			TransitionTape[i * 5 + 4] = ptr == NULL ? (turingMachine[i][4] == '2' ? NULL : NULL) : (ULONG_PTR)(TransitionTape + (idx * 5));
		}
		unsigned char* InputTape = (unsigned char*)malloc(inpSize);
		memcpy(InputTape, Input, inpSize);
		unsigned char* CurInputPtr = InputTape;
		ULONG_PTR* CurTransitionPtr = TransitionTape;
		if (InExLimUnlim & 8)
			AsmListTM((ULONG_PTR)TransitionTape, (ULONG_PTR)InputTape, (ULONG_PTR)&CurTransitionPtr, (ULONG_PTR)&CurInputPtr);
		if (bOutput) {
			printf("External assembly Turing machine: %s -> ", Input);
			fwrite(InputTape, 1, inpSize, stdout);
			printf("\n");
		}
#if !defined(_WIN64)
		if (InExLimUnlim & 4) {
			memcpy(InputTape, Input, inpSize);
			__asm {
				mov ACCUMULATOR, TransitionTape
				mov CurTransitionPtr, ACCUMULATOR
				mov ACCUMULATOR, InputTape
				mov CurInputPtr, ACCUMULATOR
				dobegin :
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
					donext :
				mov ACCUMULATOR, CurTransitionPtr
					mov ACCUMULATOR, SIZEWORD ptr[ACCUMULATOR]
					mov CurTransitionPtr, ACCUMULATOR
					check :
				cmp CurTransitionPtr, 0
					je finishlist
					jmp dobegin
					finishlist :
			}
			if (bOutput) {
				printf("Inline assembly Turing machine: %s -> ", Input);
				fwrite(InputTape, 1, inpSize, stdout);
				printf("\n");
			}
		}
#endif
		free(TransitionTape);
		free(InputTape);
	}
}

int main()
{
	char turingMachine[][5] = {
		{ '1', '0', '0', 'R', '1' },
		{ '1', '1', '1', 'R', '1' },
		{ '1', '_', '_', 'R', '3' },
		{ '3', '0', '0', 'R', '3' },
		{ '3', '1', '1', 'R', '4' },
		{ '3', '_', '_', 'R', '2' },
		{ '4', '0', '0', 'R', '4' },
		{ '4', '1', '1', 'R', '4' },
		{ '4', '_', '_', 'L', '5' },
		{ '5', '0', '1', 'L', '5' },
		{ '5', '1', '0', 'L', '6' },
		{ '6', '0', '0', 'L', '6' },
		{ '6', '1', '1', 'L', '6' },
		{ '6', '_', '_', 'L', '7' },
		{ '7', '1', '0', 'L', '7' },
		{ '7', '0', '1', 'R', '1' },
		{ '7', '_', '1', 'R', '1' }
	}; //must be sorted
	char Input[] = "0100_1001_";

	CTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, true, 3);
	AsmTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, true, 15);
	MovTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, true, 7);

	LARGE_INTEGER start;
	LARGE_INTEGER stop;
	LARGE_INTEGER frequency;
	QueryPerformanceFrequency(&frequency);
	QueryPerformanceCounter(&start);
	for (int i = 0; i < 100000; i++) {
		CTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, false, 2);
	}
	QueryPerformanceCounter(&stop);
	printf("C Turing machine: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
	QueryPerformanceCounter(&start);
	for (int i = 0; i < 100000; i++) {
		CTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, false, 1);
	}
	QueryPerformanceCounter(&stop);
	printf("C Turing machine limited transitions: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
	QueryPerformanceCounter(&start);
	for (int i = 0; i < 100000; i++) {
		AsmTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, false, 8);
	}
	QueryPerformanceCounter(&stop);
	printf("External assembly Turing machine: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
#if !defined(_WIN64)
	QueryPerformanceCounter(&start);
	for (int i = 0; i < 100000; i++) {
		AsmTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, false, 4);
	}
	QueryPerformanceCounter(&stop);
	printf("Inline assembly Turing machine: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
#endif
	QueryPerformanceCounter(&start);
	for (int i = 0; i < 100000; i++) {
		AsmTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, false, 2);
	}
	QueryPerformanceCounter(&stop);
	printf("External assembly Turing machine limited transitions: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
#if !defined(_WIN64)
	QueryPerformanceCounter(&start);
	for (int i = 0; i < 100000; i++) {
		AsmTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, false, 1);
	}
	QueryPerformanceCounter(&stop);
	printf("Inline assembly Turing machine limited transitions: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
#endif
	QueryPerformanceCounter(&start);
	for (int i = 0; i < 100000; i++) {
		MovTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, false, 2);
	}
	QueryPerformanceCounter(&stop);
	printf("External assembly mov Turing machine: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
#if !defined(_WIN64)
	QueryPerformanceCounter(&start);
	for (int i = 0; i < 100000; i++) {
		MovTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, false, 1);
	}
	QueryPerformanceCounter(&stop);
	printf("Inline assembly mov Turing machine: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
#endif
	QueryPerformanceCounter(&start);
	for (int i = 0; i < 100000; i++) {
		MovTM(turingMachine, sizeof(turingMachine), Input, sizeof(Input) - 1, false, 4);
	}
	QueryPerformanceCounter(&stop);
	printf("C mov Turing machine: %lf seconds\n", (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);

	getc(stdin);
	return 0;
}