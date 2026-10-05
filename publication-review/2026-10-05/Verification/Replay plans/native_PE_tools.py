"""Read-only x64 PE exports/imports and section representation.

Importing this helper loads no DLL and invokes no process or compiler.
"""
from pathlib import Path
import hashlib,struct

def sha256(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        while chunk:=f.read(1024*1024):h.update(chunk)
    return h.hexdigest()

def inspect_pe(path):
    path=Path(path);d=path.read_bytes()
    assert d[:2]==b'MZ','Missing DOS header'
    pe=struct.unpack_from('<I',d,0x3c)[0]
    assert d[pe:pe+4]==b'PE\0\0','Missing PE signature'
    machine,n,_,_,_,sizeopt,characteristics=struct.unpack_from('<HHIIIHH',d,pe+4)
    assert machine==0x8664,'Expected x64 image'
    opt=pe+24;assert struct.unpack_from('<H',d,opt)[0]==0x20b,'Expected PE32+'
    directories=opt+112
    sections=[]
    for j in range(n):
        at=opt+sizeopt+40*j
        vs,va,size,offset=struct.unpack_from('<IIII',d,at+8)
        flags=struct.unpack_from('<I',d,at+36)[0]
        sections.append({'name':d[at:at+8].rstrip(b'\0').decode('ascii'),
          'rva':va,'virtual_bytes':vs,'raw_bytes':size,'raw_offset':offset,'flags':flags,
          'executable':bool(flags&0x20000000),'readable':bool(flags&0x40000000),'writable':bool(flags&0x80000000)})
    def section(rva):
        return next(s for s in sections if s['rva']<=rva<s['rva']+max(s['virtual_bytes'],s['raw_bytes']))
    def offset(rva):
        s=section(rva);relative=rva-s['rva'];assert relative<s['raw_bytes'],'RVA is zero-initialized virtual data'
        result=s['raw_offset']+relative;assert result<len(d);return result
    def cstring(rva):
        at=offset(rva);end=d.index(b'\0',at);return d[at:end].decode('ascii')
    er,es=struct.unpack_from('<II',d,directories)
    exports={};export_dll_name=None
    if er:
        e=offset(er);export_dll_name=cstring(struct.unpack_from('<I',d,e+12)[0])
        ordinalbase,nfunctions,nnames,fr, nr,ordr=struct.unpack_from('<IIIIII',d,e+16)
        functions,names,ordinals=offset(fr),offset(nr),offset(ordr)
        for j in range(nnames):
            name=cstring(struct.unpack_from('<I',d,names+4*j)[0])
            index=struct.unpack_from('<H',d,ordinals+2*j)[0];assert index<nfunctions
            rva=struct.unpack_from('<I',d,functions+4*index)[0];assert rva
            sec=section(rva);rel=rva-sec['rva']
            slot=d[sec['raw_offset']+rel:sec['raw_offset']+rel+8] if rel+8<=sec['raw_bytes'] else b'\0'*8
            exports[name]={'ordinal':ordinalbase+index,'rva':rva,'section':sec['name'],
              'executable':sec['executable'],'writable':sec['writable'],
              'forwarder':cstring(rva) if er<=rva<er+es else None,
              'first_8_bytes_hex':slot.hex(),'virtual_zero_initialized':rel>=sec['raw_bytes']}
        assert len(exports)==nnames,'Repeated PE export name'
    ir,isize=struct.unpack_from('<II',d,directories+8);imports={}
    if ir:
        at=offset(ir);maximum=max(1,isize//20)
        for j in range(maximum):
            original,stamp,chain,name_rva,thunk=struct.unpack_from('<IIIII',d,at+20*j)
            if not any([original,stamp,chain,name_rva,thunk]):break
            name=cstring(name_rva);symbols=[];cursor=offset(original or thunk)
            while value:=struct.unpack_from('<Q',d,cursor)[0]:
                if value>>63:symbols.append({'ordinal':value&0xffff})
                else:
                    pos=offset(value);end=d.index(b'\0',pos+2)
                    symbols.append({'hint':struct.unpack_from('<H',d,pos)[0],'name':d[pos+2:end].decode('ascii')})
                cursor+=8
            imports[name]=symbols
    return {'file':str(path.resolve()),'sha256':sha256(path),'bytes':len(d),'x64_PE32_plus':True,
      'is_DLL':bool(characteristics&0x2000),'export_DLL_name':export_dll_name,
      'actual_export_count':len(exports),'exports':exports,'imports':imports,'sections':sections}
