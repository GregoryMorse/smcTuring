"""Windows aggregate limits for all descendants of a proof/test command."""
from __future__ import annotations
import ctypes
from ctypes import wintypes as W
import hashlib,os,threading
from pathlib import Path

MAX_BYTES=1_500_000_000
ROOT=Path(__file__).resolve().parents[1]
TAG=hashlib.sha256(str(ROOT).lower().encode()).hexdigest()[:16]
JOB_NAME='Local\\smcTuringBudget-'+TAG
MUTEX_NAME='Local\\smcTuringVerification-'+TAG
class Basic(ctypes.Structure):
 _fields_=[('ProcessTime',ctypes.c_int64),('JobTime',ctypes.c_int64),('Flags',W.DWORD),
  ('MinWorkingSet',ctypes.c_size_t),('MaxWorkingSet',ctypes.c_size_t),('ActiveProcessLimit',W.DWORD),
  ('Affinity',ctypes.c_size_t),('PriorityClass',W.DWORD),('SchedulingClass',W.DWORD)]
class IO(ctypes.Structure):
 _fields_=[(name,ctypes.c_uint64) for name in ['ReadOps','WriteOps','OtherOps','ReadBytes','WriteBytes','OtherBytes']]
class Limits(ctypes.Structure):
 _fields_=[('Basic',Basic),('IO',IO),('ProcessMemoryLimit',ctypes.c_size_t),('JobMemoryLimit',ctypes.c_size_t),
  ('PeakProcessMemory',ctypes.c_size_t),('PeakJobMemory',ctypes.c_size_t)]
class ProcessIds(ctypes.Structure):
 _fields_=[('Assigned',W.DWORD),('Count',W.DWORD),('Ids',ctypes.c_size_t*64)]
class MemoryCounters(ctypes.Structure):
 _fields_=[('Size',W.DWORD),('PageFaultCount',W.DWORD)]+[
  (name,ctypes.c_size_t) for name in ['PeakWorkingSet','WorkingSet','PeakPagedPool','PagedPool',
   'PeakNonpagedPool','NonpagedPool','Pagefile','PeakPagefile','Private']]

def api():
 if os.name!='nt':raise RuntimeError('This resource guard requires Windows; no unlimited fallback is allowed.')
 k=ctypes.WinDLL('kernel32',use_last_error=True)
 signatures={
  'CreateJobObjectW':([ctypes.c_void_p,W.LPCWSTR],W.HANDLE),
  'CreateMutexW':([ctypes.c_void_p,W.BOOL,W.LPCWSTR],W.HANDLE),
  'WaitForSingleObject':([W.HANDLE,W.DWORD],W.DWORD),
  'SetInformationJobObject':([W.HANDLE,ctypes.c_int,ctypes.c_void_p,W.DWORD],W.BOOL),
  'QueryInformationJobObject':([W.HANDLE,ctypes.c_int,ctypes.c_void_p,W.DWORD,ctypes.c_void_p],W.BOOL),
  'AssignProcessToJobObject':([W.HANDLE,W.HANDLE],W.BOOL),
  'IsProcessInJob':([W.HANDLE,W.HANDLE,ctypes.POINTER(W.BOOL)],W.BOOL),
  'GetCurrentProcess':([],W.HANDLE),
  'ReleaseMutex':([W.HANDLE],W.BOOL),
  'OpenProcess':([W.DWORD,W.BOOL,W.DWORD],W.HANDLE),
  'CloseHandle':([W.HANDLE],W.BOOL),
  'TerminateProcess':([W.HANDLE,W.UINT],W.BOOL),
  'K32GetProcessMemoryInfo':([W.HANDLE,ctypes.POINTER(MemoryCounters),W.DWORD],W.BOOL)}
 for name,(args,result) in signatures.items():
  fn=getattr(k,name);fn.argtypes=args;fn.restype=result
 return k
def checked(result):
 if not result:raise ctypes.WinError(ctypes.get_last_error())
 return result
class Budget:
 def __init__(self,limit=MAX_BYTES):
  if not 64_000_000<=limit<=MAX_BYTES:raise ValueError('Memory cap must be between 64 MB and 1.5 GB.')
  self.limit=limit;self.k=api()
  self.mutex=checked(self.k.CreateMutexW(None,False,MUTEX_NAME))
  locked=self.k.WaitForSingleObject(self.mutex,0)
  if locked not in [0,0x80]:raise RuntimeError('Another verification command is active; run checks serially.')
  self.job=checked(self.k.CreateJobObjectW(None,JOB_NAME))
  info=Limits();info.Basic.Flags=0x8|0x200|0x2000
  info.Basic.ActiveProcessLimit=8;info.JobMemoryLimit=limit
  checked(self.k.SetInformationJobObject(self.job,9,ctypes.byref(info),ctypes.sizeof(info)))
  checked(self.k.AssignProcessToJobObject(self.job,self.k.GetCurrentProcess()))
  os.environ['SMCTURING_MEMORY_BUDGET']=str(limit)
 def processes(self):
  info=ProcessIds();checked(self.k.QueryInformationJobObject(self.job,3,ctypes.byref(info),ctypes.sizeof(info),None))
  if info.Count!=info.Assigned or info.Count>64:raise RuntimeError('Incomplete job process inventory')
  return list(info.Ids[:info.Count])
 def resident(self):
  total=0
  for pid in self.processes():
   handle=self.k.OpenProcess(0x1000,False,pid)
   if not handle:
    if ctypes.get_last_error() in [6,87]:continue
    raise ctypes.WinError(ctypes.get_last_error())
   try:
    inside=W.BOOL();checked(self.k.IsProcessInJob(handle,self.job,ctypes.byref(inside)))
    if not inside.value:continue
    info=MemoryCounters();info.Size=ctypes.sizeof(info)
    if self.k.K32GetProcessMemoryInfo(handle,ctypes.byref(info),ctypes.sizeof(info)):
     total+=info.WorkingSet
    elif ctypes.get_last_error() not in [6,87,299]:raise ctypes.WinError(ctypes.get_last_error())
   finally:self.k.CloseHandle(handle)
  return total
 def stop_children(self):
  for pid in self.processes():
   if pid==os.getpid():continue
   handle=self.k.OpenProcess(0x1000|1,False,pid)
   if not handle:continue
   try:
    inside=W.BOOL();checked(self.k.IsProcessInJob(handle,self.job,ctypes.byref(inside)))
    if inside.value:self.k.TerminateProcess(handle,137)
   finally:self.k.CloseHandle(handle)
 def report(self):
  info=Limits();checked(self.k.QueryInformationJobObject(self.job,9,ctypes.byref(info),ctypes.sizeof(info),None))
  return dict(memory_limit_bytes=info.JobMemoryLimit,peak_group_commit_bytes=info.PeakJobMemory,
   peak_process_commit_bytes=info.PeakProcessMemory,maximum_processes=info.Basic.ActiveProcessLimit,
   maximum_process_working_set_bytes=info.Basic.MaxWorkingSet)
 def release(self):
  checked(self.k.ReleaseMutex(self.mutex))
  # Keep the job handle until process exit. Closing it explicitly would kill
  # this launcher. The kernel closes it at exit and kills remaining descendants.
def require_budget():
 k=api();job=checked(k.CreateJobObjectW(None,JOB_NAME));inside=W.BOOL()
 try:
  checked(k.IsProcessInJob(k.GetCurrentProcess(),job,ctypes.byref(inside)))
  info=Limits();checked(k.QueryInformationJobObject(job,9,ctypes.byref(info),ctypes.sizeof(info),None))
  if not inside.value or not info.Basic.Flags&0x200 or not 0<info.JobMemoryLimit<=MAX_BYTES:
   raise RuntimeError('Use python validation/limited_run.py -- COMMAND; unrestricted verification is disabled.')
 finally:k.CloseHandle(job)

class ResidentMonitor:
 """Sample all job working sets and stop descendants at a conservative threshold.

 The allocation limit is enforced by Windows. This working-set check is sampled,
 not an instantaneous OS quota. Shared pages are counted per process, deliberately
 overestimating the physical resident usage.
 """
 def __init__(self,budget):
  self.budget=budget;self.peak=0;self.error=None;self.stop=threading.Event()
  self.interval=0.025;self.thread=threading.Thread(target=self.run,daemon=True)
 def sample(self):
  self.peak=max(self.peak,self.budget.resident())
  if self.peak>self.budget.limit:raise RuntimeError('Aggregate resident-memory threshold exceeded')
 def run(self):
  while not self.stop.is_set():
   try:self.sample()
   except Exception as exc:
    self.error=str(exc);self.budget.stop_children();return
   self.stop.wait(self.interval)
 def start(self):
  self.sample();self.thread.start()
 def finish(self):
  self.stop.set()
  if self.thread.ident is not None:self.thread.join()
  return dict(sampled_peak_group_resident_bytes=self.peak,
   resident_stop_threshold_bytes=self.budget.limit,resident_sample_interval_ms=25,
   resident_monitor_error=self.error)
