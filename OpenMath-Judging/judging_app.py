"""Native desktop judging library, backed by local SQLite and original files."""
import pathlib, json, sqlite3, tkinter as tk
from tkinter import ttk, messagebox, filedialog
from library_core import CATEGORIES, TOPICS, connect, read_bytes, materialize
import sys
if sys.platform=='win32':
    import ctypes
    try:ctypes.windll.user32.SetProcessDpiAwarenessContext(ctypes.c_void_p(-4))
    except (AttributeError,OSError):pass

ROOT=pathlib.Path(__file__).resolve().parent

class JudgingApp:
    PAGE=200
    def __init__(self,window):
        self.window=window; self.db=connect(ROOT); self.team_id=None; self.category=None; self.offset=0; self.current_file=None; self.search_after=None
        window.title('OpenMath Judging — person and problem review'); window.geometry(f'{min(1460,window.winfo_screenwidth()-60)}x{min(920,window.winfo_screenheight()-100)}'); window.minsize(1000,620)
        style=ttk.Style(); style.theme_use('clam'); style.configure('Treeview',rowheight=25); style.configure('TButton',padding=5)
        header=ttk.Frame(window,padding=12); header.pack(fill='x')
        ttk.Label(header,text='OpenMath Judging',font=('Segoe UI',20,'bold')).pack(side='left')
        stats=self.db.execute('SELECT (SELECT COUNT(*) FROM teams WHERE id!="EVENT"), (SELECT COUNT(*) FROM files)').fetchone()
        ttk.Label(header,text=f'  {stats[0]} grouped records + event sources · {stats[1]:,} local file entries',font=('Segoe UI',11)).pack(side='left')
        panes=ttk.Panedwindow(window,orient='horizontal'); panes.pack(fill='both',expand=True,padx=12,pady=(0,12))
        left=ttk.Frame(panes); right=ttk.Frame(panes); panes.add(left,weight=1); panes.add(right,weight=4)
        self.team_search=tk.StringVar(); ttk.Entry(left,textvariable=self.team_search).pack(fill='x',pady=(0,6)); self.team_search.trace_add('write',lambda *_:self.populate_teams())
        self.team_filter=tk.StringVar(value='All records'); box=ttk.Combobox(left,textvariable=self.team_filter,values=['All records','With contestant files','Potential entrants','Interest / organizer / withdrawal'],state='readonly');box.pack(fill='x');box.bind('<<ComboboxSelected>>',lambda *_:self.populate_teams())
        self.teams=ttk.Treeview(left,columns=('files',),show='tree headings');self.teams.heading('#0',text='Contestant / team');self.teams.heading('files',text='Files');self.teams.column('#0',width=250);self.teams.column('files',width=65,stretch=False,anchor='e')
        self.teams.pack(fill='both',expand=True,pady=6);self.teams.bind('<<TreeviewSelect>>',self.select_team)
        self.categories=ttk.Treeview(left,show='tree',height=14);self.categories.pack(fill='x');self.categories.bind('<<TreeviewSelect>>',self.select_category)
        self.title=tk.StringVar(value='Choose a contestant');ttk.Label(right,textvariable=self.title,font=('Segoe UI',15,'bold'),wraplength=950).pack(anchor='w',pady=5)
        notebook=ttk.Notebook(right);notebook.pack(fill='both',expand=True);self.notebook=notebook
        summary=ttk.Frame(notebook);files=ttk.Frame(notebook);notes=ttk.Frame(notebook);notebook.add(summary,text='Team and submission');notebook.add(files,text='Classified files');notebook.add(notes,text='Review notes')
        self.file_tab=files
        self.summary=tk.Text(summary,wrap='word',font=('Segoe UI',11),padx=14,pady=12);self.summary.pack(fill='both',expand=True);self.summary.configure(state='disabled')
        bar=ttk.Frame(files,padding=5);bar.pack(fill='x')
        self.file_search=tk.StringVar();ttk.Entry(bar,textvariable=self.file_search,width=42).pack(side='left');self.file_search.trace_add('write',self.schedule_search)
        self.topic=tk.StringVar(value='All topics'); topics=ttk.Combobox(bar,textvariable=self.topic,values=['All topics']+TOPICS,state='readonly',width=27);topics.pack(side='left',padx=5);topics.bind('<<ComboboxSelected>>',lambda *_:self.load_files(reset=True))
        ttk.Button(bar,text='Search',command=lambda:self.load_files(reset=True)).pack(side='left')
        self.page_text=tk.StringVar();ttk.Label(bar,textvariable=self.page_text).pack(side='left',padx=8)
        ttk.Button(bar,text='Previous',command=lambda:self.page(-1)).pack(side='right');ttk.Button(bar,text='Next',command=lambda:self.page(1)).pack(side='right')
        split=ttk.Panedwindow(files,orient='vertical');split.pack(fill='both',expand=True)
        table=ttk.Frame(split);preview=ttk.Frame(split);split.add(table,weight=2);split.add(preview,weight=2)
        self.files=ttk.Treeview(table,columns=('category','topic','size','version'),show='tree headings');self.files.heading('#0',text='Original filename / path');self.files.column('#0',width=500)
        for key,label,width in [('category','Purpose',170),('topic','Problem / topic',155),('size','Bytes',85),('version','Version',190)]:self.files.heading(key,text=label);self.files.column(key,width=width,stretch=True)
        sy=ttk.Scrollbar(table,orient='vertical',command=self.files.yview);sx=ttk.Scrollbar(table,orient='horizontal',command=self.files.xview);self.files.configure(yscrollcommand=sy.set,xscrollcommand=sx.set);self.files.grid(row=0,column=0,sticky='nsew');sy.grid(row=0,column=1,sticky='ns');sx.grid(row=1,column=0,sticky='ew');table.rowconfigure(0,weight=1);table.columnconfigure(0,weight=1)
        self.files.bind('<<TreeviewSelect>>',self.select_file);self.files.bind('<Double-1>',lambda *_:self.export_file())
        controls=ttk.Frame(preview,padding=5);controls.pack(fill='x')
        ttk.Button(controls,text='Save selected file as…',command=self.export_file).pack(side='left')
        self.category_edit=tk.StringVar();ttk.Combobox(controls,textvariable=self.category_edit,values=list(CATEGORIES.values()),state='readonly',width=32).pack(side='left',padx=5)
        self.topic_edit=tk.StringVar();ttk.Combobox(controls,textvariable=self.topic_edit,values=TOPICS,state='readonly',width=25).pack(side='left')
        ttk.Button(controls,text='Apply classification',command=self.reclassify).pack(side='left',padx=5)
        self.preview=tk.Text(preview,wrap='none',font=('Consolas',10),padx=8,pady=8);self.preview.pack(fill='both',expand=True);self.preview.configure(state='disabled')
        self.note=tk.Text(notes,wrap='word',font=('Segoe UI',11),padx=14,pady=12);self.note.pack(fill='both',expand=True)
        ttk.Button(notes,text='Save this team’s review notes',command=self.save_note).pack(anchor='e',padx=10,pady=8)
        self.assessment_data=None;self.assessment_path=ROOT/'judging/preliminary-assessment.json'
        self.review_data=None;review_path=ROOT/'review/review-data.json'
        if review_path.exists():
            self.review_data=json.loads(review_path.read_text(encoding='utf-8'));self.build_compact_tabs(notebook)
        elif self.assessment_path.exists():
            self.assessment_data=json.loads(self.assessment_path.read_text(encoding='utf-8'))
            self.build_assessment_tabs(notebook)
        self.status=tk.StringVar(value='Select a team, then a category. Double-click saves a copy; no contestant code is run.');ttk.Label(window,textvariable=self.status,padding=7).pack(fill='x')
        self.populate_teams()
        children=self.teams.get_children()
        if 'E08' in children:self.teams.selection_set('E08');self.teams.see('E08');self.select_team()
        if self.review_data:self.notebook.select(self.compact_tab)
        elif self.assessment_data:self.notebook.select(self.assessment_tab)
        window.protocol('WM_DELETE_WINDOW',self.close)

    def populate_teams(self):
        q=self.team_search.get().casefold(); filt=self.team_filter.get();current=self.team_id
        self.teams.delete(*self.teams.get_children())
        rows=self.db.execute('SELECT t.*, COUNT(f.id) AS file_count, SUM(CASE WHEN f.category NOT IN ("12-correspondence","13-archives") AND f.source!="Collected official hill leaderboards" THEN 1 ELSE 0 END) AS work_files FROM teams t LEFT JOIN files f ON f.team_id=t.id GROUP BY t.id ORDER BY t.id').fetchall()
        for row in rows:
            authors=' '.join(next((t['authors'] for t in self.review_data['teams'] if t['id']==row['id']),[])) if self.review_data else ''
            if q not in (row['name']+' '+row['aliases']+' '+row['id']+' '+authors).casefold():continue
            if filt=='With contestant files' and not row['work_files']:continue
            if filt=='Potential entrants' and not row['potential']:continue
            if filt=='Interest / organizer / withdrawal' and row['potential']:continue
            self.teams.insert('', 'end',iid=row['id'],text=row['id']+' '+row['name'],values=(f"{row['file_count']:,}",))
        if current and self.teams.exists(current):self.teams.selection_set(current)

    def select_team(self,event=None):
        selection=self.teams.selection()
        if not selection:return
        new=selection[0];previous=self.team_id
        if self.team_id and new!=self.team_id:self.persist_note()
        self.team_id=new;row=self.db.execute('SELECT * FROM teams WHERE id=?',(new,)).fetchone();self.title.set(row['name'])
        self.write_text(self.summary,row['overview'])
        if self.assessment_data:self.load_assessment()
        if self.review_data:self.load_compact_profile()
        if new!=previous:
            note=self.db.execute('SELECT body FROM notes WHERE team_id=?',(new,)).fetchone();self.note.delete('1.0','end');self.note.insert('1.0',note['body'] if note else '')
        self.categories.delete(*self.categories.get_children());total=self.db.execute('SELECT COUNT(*) FROM files WHERE team_id=?',(new,)).fetchone()[0]
        self.categories.insert('', 'end',iid='all',text=f'All files ({total:,})')
        counts=dict(self.db.execute('SELECT category,COUNT(*) FROM files WHERE team_id=? GROUP BY category',(new,)).fetchall())
        for cat,label in CATEGORIES.items():self.categories.insert('', 'end',iid=cat,text=f'{label} ({counts.get(cat,0):,})')
        self.category=None;self.categories.selection_set('all');self.load_files(reset=True)

    def select_category(self,event=None):
        selected=self.categories.selection()
        if not selected:return
        self.category=None if selected[0]=='all' else selected[0];self.load_files(reset=True)
        if event is not None:self.notebook.select(self.file_tab)

    def schedule_search(self,*_):
        if self.search_after:self.window.after_cancel(self.search_after)
        self.search_after=self.window.after(300,lambda:self.load_files(reset=True))

    def file_where(self):
        parts=['team_id=?'];values=[self.team_id]
        if self.category:parts.append('category=?');values.append(self.category)
        if self.topic.get()!='All topics':parts.append('topic=?');values.append(self.topic.get())
        q=self.file_search.get().strip()
        if q:parts.append('(original_path LIKE ? OR version LIKE ? OR source LIKE ?)');values.extend(['%'+q+'%']*3)
        return ' AND '.join(parts),values

    def load_files(self,reset=False):
        if not self.team_id:return
        if reset:self.offset=0
        where,values=self.file_where();self.match_count=self.db.execute('SELECT COUNT(*) FROM files WHERE '+where,values).fetchone()[0]
        self.offset=max(0,min(self.offset,((max(1,self.match_count)-1)//self.PAGE)*self.PAGE))
        rows=self.db.execute('SELECT * FROM files WHERE '+where+' ORDER BY category,original_path,id LIMIT ? OFFSET ?',values+[self.PAGE,self.offset]).fetchall()
        self.files.delete(*self.files.get_children())
        for row in rows:self.files.insert('','end',iid=str(row['id']),text=row['original_path'],values=(CATEGORIES[row['category']],row['topic'],f"{row['bytes']:,}",row['version']))
        self.current_file=None;self.write_text(self.preview,'Select a file to see its source, classification and content. Every archive member is available locally, including large result datasets.')
        self.page_text.set(f'{self.offset+1 if rows else 0}–{self.offset+len(rows)} of {self.match_count:,}')

    def page(self,direction):self.offset+=direction*self.PAGE;self.load_files()

    @staticmethod
    def write_text(widget,text):widget.configure(state='normal');widget.delete('1.0','end');widget.insert('1.0',text);widget.configure(state='disabled')

    def select_file(self,event=None):
        selected=self.files.selection()
        if not selected:return
        row=self.db.execute('SELECT * FROM files WHERE id=?',(int(selected[0]),)).fetchone();self.current_file=row
        self.category_edit.set(CATEGORIES[row['category']]);self.topic_edit.set(row['topic'])
        meta=f"Original path: {row['original_path']}\nPurpose: {CATEGORIES[row['category']]}\nTopic: {row['topic']}\nBasis: {row['basis']}\nSource: {row['source']}\nVersion: {row['version']}\nIntegrity: {row['verification']}\nLocal storage: {row['local_path'] or row['archive_path']+' :: '+row['archive_member']}\nSHA-256: {row['sha256'] or 'Member CRC recorded; original archive SHA-256 recorded'}\n\n"
        try:
            data=read_bytes(ROOT,row,1024*1024+1)
            if b'\0' in data[:5000] or pathlib.PurePosixPath(row['original_path']).suffix.lower() in ('.pdf','.zip','.png','.jpg','.jpeg','.gif','.npz','.npy','.docx','.mp4'):
                body='Binary file. Use “Save selected file as…” to read it in your preferred application.'
            else:body=data[:1024*1024].decode('utf-8',errors='replace')+('\n\n[Preview limited to 1 MiB; full file is available.]' if len(data)>1024*1024 else '')
        except Exception as exc:body='Unable to read file: '+str(exc)
        reviewed=self.db.execute('SELECT summary,method,content_read_bytes FROM file_reviews WHERE file_id=?',(row['id'],)).fetchone() if self.review_data else None
        if reviewed:meta='FILE SUMMARY\n'+reviewed['summary']+'\nMethod: '+reviewed['method']+'; content bytes inspected: '+str(reviewed['content_read_bytes'])+'\n\n'+meta
        self.write_text(self.preview,meta+body)

    def export_file(self):
        if self.current_file is None:return
        row=self.current_file
        name=pathlib.PurePosixPath(row['original_path']).name
        dest=filedialog.asksaveasfilename(title='Save a local copy',initialdir=str(ROOT/'contestants'/row['team_id']),initialfile=name)
        if not dest:return
        try:
            data=read_bytes(ROOT,row);pathlib.Path(dest).write_bytes(data);self.status.set('Saved '+dest)
        except Exception as exc:messagebox.showerror('Could not save file',str(exc))

    def reclassify(self):
        if self.current_file is None:return
        category=next(k for k,v in CATEGORIES.items() if v==self.category_edit.get())
        self.db.execute('UPDATE files SET category=?,topic=?,basis=? WHERE id=?',(category,self.topic_edit.get(),'User classification override',self.current_file['id']));self.db.commit();self.select_team();self.status.set('Classification saved locally.')

    def persist_note(self):
        if not self.team_id:return
        body=self.note.get('1.0','end-1c');self.db.execute('INSERT INTO notes(team_id,body) VALUES(?,?) ON CONFLICT(team_id) DO UPDATE SET body=excluded.body',(self.team_id,body));self.db.commit()
        (ROOT/'contestants'/self.team_id/'REVIEW-NOTES.txt').write_text(body,encoding='utf-8')

    def save_note(self):self.persist_note();self.status.set('Review notes saved locally.')
    def close(self):self.persist_note();self.db.close();self.window.destroy()

    def build_compact_tabs(self,notebook):
        frame=ttk.Frame(notebook);notebook.insert(0,frame,text='Person / entry review');self.compact_tab=frame
        bar=ttk.Frame(frame,padding=6);bar.pack(fill='x');ttk.Label(bar,text='Review person (shared packet):').pack(side='left')
        self.person_choice=tk.StringVar();self.person_picker=ttk.Combobox(bar,textvariable=self.person_choice,values=[x['display_name']+' • '+x['entrant_id'] for x in self.review_data['people']],state='readonly',width=78);self.person_picker.pack(side='left',padx=8);self.person_picker.bind('<<ComboboxSelected>>',self.select_compact_person)
        self.compact_text=tk.Text(frame,wrap='word',font=('Segoe UI',11),padx=14,pady=12)
        scroll=ttk.Scrollbar(frame,command=self.compact_text.yview);self.compact_text.configure(yscrollcommand=scroll.set);scroll.pack(side='right',fill='y');self.compact_text.pack(fill='both',expand=True);self.compact_text.configure(state='disabled')
        problems=ttk.Frame(notebook);notebook.insert(1,problems,text='Problem profiles')
        split=ttk.Panedwindow(problems,orient='horizontal');split.pack(fill='both',expand=True);left=ttk.Frame(split);right=ttk.Frame(split);split.add(left,weight=1);split.add(right,weight=3)
        self.problem_table=ttk.Treeview(left,columns=('D','entries'),show='tree headings');self.problem_table.heading('#0',text='Family');self.problem_table.column('#0',width=195);self.problem_table.heading('D',text='D');self.problem_table.column('D',width=50);self.problem_table.heading('entries',text='Results');self.problem_table.column('entries',width=55)
        ps=ttk.Scrollbar(left,command=self.problem_table.yview);self.problem_table.configure(yscrollcommand=ps.set);ps.pack(side='right',fill='y');self.problem_table.pack(fill='both',expand=True)
        self.problem_text=tk.Text(right,wrap='word',font=('Segoe UI',11),padx=12,pady=12);ss=ttk.Scrollbar(right,command=self.problem_text.yview);self.problem_text.configure(yscrollcommand=ss.set);ss.pack(side='right',fill='y');self.problem_text.pack(fill='both',expand=True);self.problem_text.configure(state='disabled')
        for k,p in self.review_data['problems'].items():self.problem_table.insert('','end',iid=k,text=k,values=(p['D_0_1000_proposed'],len(p['result_ids'])+len(p.get('supporting_result_ids',[]))))
        self.problem_table.bind('<<TreeviewSelect>>',self.select_compact_problem)
        self.problem_table.selection_set('KOBON');self.select_compact_problem()
        tally=ttk.Frame(notebook);notebook.insert(2,tally,text='Proposed scores')
        ttk.Label(tally,text='Review proposals, not awards. S=sum of distinct family unions; A=largest. M2 is separate. New D/admission and formal checks need sign-off.',wraplength=940,padding=8).pack(fill='x')
        self.compact_tally=ttk.Treeview(tally,columns=('S','A','M2','minutes'),show='tree headings');self.compact_tally.heading('#0',text='Entry');self.compact_tally.column('#0',width=480)
        for k,l in [('S','Proposed S'),('A','Proposed A'),('M2','M2 count / adjusted'),('minutes','Minutes')]:self.compact_tally.heading(k,text=l);self.compact_tally.column(k,width=140)
        ss=ttk.Scrollbar(tally,command=self.compact_tally.yview);self.compact_tally.configure(yscrollcommand=ss.set);ss.pack(side='right',fill='y');self.compact_tally.pack(fill='both',expand=True)
        for t in self.review_data['teams']:self.compact_tally.insert('','end',iid=t['id'],text=t['id']+' '+t['name'],values=(f"{float(t['adjusted_S']):.3f}",f"{float(t['adjusted_A']):.3f}",str(t['M2_proposed_integer_count'])+' / '+t['M2_adjusted_overall_value'],t['review_minutes']))
        self.compact_tally.bind('<<TreeviewSelect>>',self.select_compact_tally)

    def load_compact_profile(self):
        path=ROOT/'review/people'/(self.team_id+'.txt')
        prefix='PERSON: '+self.person_choice.get().rsplit(' • ',1)[0]+'\nShared packet attribution; no unsupported individual point split.\n\n' if self.person_choice.get().endswith(' • '+self.team_id) else ''
        self.write_text(self.compact_text,prefix+path.read_text(encoding='utf8') if path.exists() else 'Event handbook and shared sources; no entrant score.')

    def select_compact_person(self,event=None):
        entry=self.person_choice.get().rsplit(' • ',1)[-1];self.team_filter.set('All records');self.team_search.set('');self.populate_teams()
        if self.teams.exists(entry):self.teams.selection_set(entry);self.teams.see(entry);self.select_team();self.notebook.select(self.compact_tab)

    def select_compact_problem(self,event=None):
        ids=self.problem_table.selection()
        if ids:self.write_text(self.problem_text,(ROOT/'review/problems'/(ids[0]+'.txt')).read_text(encoding='utf8'))

    def select_compact_tally(self,event=None):
        ids=self.compact_tally.selection()
        if ids and self.teams.exists(ids[0]):self.teams.selection_set(ids[0]);self.teams.see(ids[0]);self.select_team();self.notebook.select(self.compact_tab)

    def build_assessment_tabs(self,notebook):
        frame=ttk.Frame(notebook);notebook.add(frame,text='Assessment');self.assessment_tab=frame
        ttk.Label(frame,text='Draft review: difficulty, progress and evidence are separate. Official acceptance and scores remain unawarded.',wraplength=920,padding=8).pack(fill='x')
        split=ttk.Panedwindow(frame,orient='vertical');split.pack(fill='both',expand=True)
        top=ttk.Frame(split);bottom=ttk.Frame(split);split.add(top,weight=1);split.add(bottom,weight=3)
        self.result_table=ttk.Treeview(top,columns=('modality','progress','difficulty'),show='tree headings',height=8)
        self.result_table.heading('#0',text='Distinct result / supporting claim');self.result_table.column('#0',width=550)
        for key,label,width in [('modality','Track',85),('progress','Proposed p',125),('difficulty','Intrinsic OPDP /10',150)]:self.result_table.heading(key,text=label);self.result_table.column(key,width=width)
        scroll=ttk.Scrollbar(top,orient='vertical',command=self.result_table.yview);self.result_table.configure(yscrollcommand=scroll.set);self.result_table.pack(side='left',fill='both',expand=True);scroll.pack(side='right',fill='y')
        self.result_table.bind('<<TreeviewSelect>>',self.select_assessment_result)
        self.assessment_detail=tk.Text(bottom,wrap='word',font=('Segoe UI',11),padx=12,pady=12);self.assessment_detail.pack(fill='both',expand=True);self.assessment_detail.configure(state='disabled')
        tally=ttk.Frame(notebook);notebook.add(tally,text='Tally')
        ttk.Label(tally,text='70 grouped records. Priced subtotals use published D candidates only; unmatched families stay symbolic. M2 is separate. These are not final standings.',wraplength=900,padding=8).pack(fill='x')
        self.tally_table=ttk.Treeview(tally,columns=('class','S','A','unpriced','M2'),show='tree headings',height=12);self.tally_table.heading('#0',text='Entrant');self.tally_table.column('#0',width=300)
        for key,label,width in [('class','Class (provisional)',170),('S','Priced S*',110),('A','Priced A*',110),('unpriced','Unpriced',75),('M2','M2 candidates ≤',100)]:self.tally_table.heading(key,text=label);self.tally_table.column(key,width=width)
        ts=ttk.Scrollbar(tally,orient='vertical',command=self.tally_table.yview);self.tally_table.configure(yscrollcommand=ts.set);self.tally_table.pack(fill='both',expand=True)
        for t in self.assessment_data['teams']:self.tally_table.insert('', 'end',iid=t['id'],text=t['id']+' '+t['name'],values=(t['entrant_class'],t['adjusted_priced_S_subtotal'],t['adjusted_priced_A_subtotal'],len(t['unpriced_families']),t['M2_potential_distinct_count_upper_bound']))
        self.tally_detail=tk.Text(tally,wrap='word',font=('Segoe UI',10),height=8,padx=10,pady=10);self.tally_detail.pack(fill='x');self.tally_detail.configure(state='disabled');self.tally_table.bind('<<TreeviewSelect>>',self.show_tally)
        synergy=ttk.Frame(notebook);notebook.add(synergy,text='Synergy');self.synergy_text=tk.Text(synergy,wrap='word',font=('Segoe UI',11),padx=14,pady=12);self.synergy_text.pack(fill='both',expand=True)
        lines=['Cross-team reuse and scientific deduplication. No synergy bonus awarded.','']
        for e in self.assessment_data['synergies']:lines.extend([e['family']+' — '+', '.join(e['teams']),e['relationship'],e['concrete_reuse'],'Limits: '+e['scope_limits'],''])
        self.write_text(self.synergy_text,'\n'.join(lines))

    def load_assessment(self):
        self.result_table.delete(*self.result_table.get_children())
        rows=[r for r in self.assessment_data['results'] if r['team_id']==self.team_id]
        for r in rows:
            f=self.assessment_data['families'].get(r['family_id']);score=f['intrinsic_opdp']['score'] if f else 'N/A'
            self.result_table.insert('', 'end',iid=r['id'],text=r['title'],values=(r['modality_proposal'],r['p_scope_if_claim_valid'] or 'N/A',score))
        if rows:self.result_table.selection_set(rows[0]['id']);self.select_assessment_result()
        else:self.write_text(self.assessment_detail,'Shared event references. Read the handbook under Classified files; no entrant score.')

    def select_assessment_result(self,event=None):
        ids=self.result_table.selection()
        if not ids:return
        r=next(x for x in self.assessment_data['results'] if x['id']==ids[0]);f=self.assessment_data['families'].get(r['family_id'])
        fields=[r['id']+' — '+r['title'],'Problem category: '+r['problem_category'],'Exact claim: '+r['exact_claim']]
        if f:
            fields+=['Difficulty: intrinsic OPDP '+str(f['intrinsic_opdp']['score'])+'/10. '+f['intrinsic_opdp']['rationale'],'Factors: '+str(f['intrinsic_opdp']['factors']),'Competition D: '+f['competition_D_status']]
            if f['published_D_candidate']:fields+=['Published 0–1000 candidate (pending scale/target binding): '+str(f['published_D_candidate']['value'])]
        fields+=['Improvement: '+r['progress_band']+'; proposed p='+str(r['p_scope_if_claim_valid']),r['progress_rationale'],'Formalization / correctness: '+r['formalization_and_correctness'],'Remaining acceptance checks:\n'+'\n'.join('• '+x for x in r['acceptance_gaps']),'Conditional family formula: '+str(r['conditional_score_formula']),'Published-candidate scenario points: '+str(r['conditional_points_published_candidate']),'Catalogue source file IDs: '+', '.join(map(str,r['catalogue_file_ids'])),'Official acceptance and score: unawarded.']
        self.write_text(self.assessment_detail,'\n\n'.join(fields))

    def show_tally(self,event=None):
        ids=self.tally_table.selection()
        if not ids:return
        t=next(x for x in self.assessment_data['teams'] if x['id']==ids[0]);lines=[t['name'],t['score_status'],'Conditional S: '+t['conditional_total_S_formula'],'Conditional A: '+t['conditional_A_formula'],'M2 potential family ceiling: '+str(t['M2_potential_distinct_count_upper_bound'])+'; approved count unassigned.']
        if t.get('exception_note'):lines.append(t['exception_note'])
        self.write_text(self.tally_detail,'\n\n'.join(lines))

if __name__=='__main__':
    window=tk.Tk();app=JudgingApp(window)
    import sys
    if '--self-test' in sys.argv:
        window.update();assert app.team_id=='E08';assert len(app.teams.get_children())>=69;assert app.files.get_children()
        first=app.files.get_children()[0];app.files.selection_set(first);app.select_file();assert app.current_file
        if app.review_data:
            assert len(app.person_picker['values'])==80
            assert len(app.compact_tally.get_children())==70
            assert len(app.problem_table.get_children())==70
            assert 'FILE SUMMARY' in app.preview.get('1.0','end')
            app.teams.selection_set('E06');app.select_team();assert '0.8' in app.compact_text.get('1.0','end')
            app.problem_table.selection_set('COLLATZ');app.select_compact_problem();assert '1765' in app.problem_text.get('1.0','end')
            app.teams.selection_set('E09');app.select_team();assert 'Current proposal0' in app.compact_text.get('1.0','end')
            app.teams.selection_set('E02');app.select_team();assert '1697.401122' in app.compact_text.get('1.0','end')
            if '--screenshot' in sys.argv:
                from PIL import ImageGrab
                app.notebook.select(app.compact_tab);window.update()
                bounds=(window.winfo_rootx(),window.winfo_rooty(),window.winfo_rootx()+window.winfo_width(),window.winfo_rooty()+window.winfo_height())
                ImageGrab.grab(bbox=bounds).save(ROOT/'review/native-review-preview.png')
        if app.assessment_data:
            assert app.result_table.get_children();assert len(app.tally_table.get_children())==70
            app.tally_table.selection_set('E06');app.show_tally();assert '.8' in app.tally_detail.get('1.0','end')
            app.teams.selection_set('E02');app.select_team();assert len(app.result_table.get_children())==27
            app.teams.selection_set('E57');app.select_team();assert len(app.result_table.get_children())==67
            if '--screenshot' in sys.argv:
                from PIL import ImageGrab
                app.teams.selection_set('E02');app.select_team();window.update();app.notebook.select(app.assessment_tab);window.update()
                bounds=(window.winfo_rootx(),window.winfo_rooty(),window.winfo_rootx()+window.winfo_width(),window.winfo_rooty()+window.winfo_height())
                ImageGrab.grab(bbox=bounds).save(ROOT/'judging/native-assessment-preview.png')
        report={'native_window_created':True,'teams_visible':len(app.teams.get_children()),'selected_team':app.team_id,'file_preview_loaded':True,'file_rows_on_page':len(app.files.get_children()),'assessment_loaded':bool(app.assessment_data),'tally_rows':len(app.tally_table.get_children()) if app.assessment_data else 0,'synergy_tab_loaded':bool(app.assessment_data)}
        if app.review_data:report.update(compact_review_loaded=True,proposed_tally_rows=len(app.compact_tally.get_children()),problem_profiles=len(app.problem_table.get_children()),person_profiles=len(app.person_picker['values']),file_summaries_loaded=True,score_exceptions_verified=True)
        (ROOT/'native-app-verification.json').write_text(json.dumps(report,indent=2),encoding='utf-8');app.db.close();window.destroy();print(json.dumps(report))
    else:
        import os,datetime
        def record_start():
            (ROOT/'app-started.json').write_text(json.dumps({'started_at':datetime.datetime.now().astimezone().isoformat(timespec='seconds'),'pid':os.getpid(),'native_window_mapped':bool(window.winfo_ismapped()),'catalogue_open':True},indent=2),encoding='utf-8')
        window.after(200,record_start);window.mainloop()
