(function(){
'use strict';
/* =====================================================================
   STREET KINGS: حواري القاهرة  —  single-file 3D street football
   Three.js r128 (CDN) · procedural everything · Web Audio synth
   ===================================================================== */
const $=id=>document.getElementById(id);
const rnd=Math.random, clamp=(v,a,b)=>v<a?a:v>b?b:v, lerp=(a,b,t)=>a+(b-a)*t, rr=(a,b)=>a+(b-a)*rnd();
const gauss=()=>(rnd()+rnd()+rnd()-1.5)*2;
function angDiff(a,b){let d=b-a;while(d>Math.PI)d-=2*Math.PI;while(d<-Math.PI)d+=2*Math.PI;return d;}
const FONT='"Segoe UI","Noto Sans Arabic","Noto Naskh Arabic",Tahoma,Arial,sans-serif';

/* ---------- storage (fails gracefully) ---------- */
const store={get(k,d){try{const v=localStorage.getItem('sk_'+k);return v===null?d:JSON.parse(v);}catch(e){return d;}},
             set(k,v){try{localStorage.setItem('sk_'+k,JSON.stringify(v));}catch(e){}}};
const settings={sound:store.get('sound',true),dur:store.get('dur',120),wins:store.get('wins',0),played:store.get('played',0),best:store.get('best',0)};
if([120,60,20].indexOf(settings.dur)<0) settings.dur=120;

/* ---------- constants ---------- */
const PW=8, PL=13, GW=2, GH=2.0, BR=0.22, GRAV=14, STEP=1/60;
const DIFF={aiSpeed:4.6,aiShotSpeed:[13,22],aiShotErr:0.075,gkReact:[0.13,0.3],gkSkill:0.84,gkAimErr:0.55,tackleVsHuman:0.36,tackleVsAI:0.44};

/* ---------- state ---------- */
let renderer,scene,camera,dirLight,mode='loading',state='menu',pausedFrom='play';
let ball,ballMesh,ringMesh,arrowMesh,aimGroup,dust,fpMesh,fpIdx=0,fpDummy;
let P=[],TM=[[],[]],specs=[],walkers=[],laundry=[],plan=[{chaser:null},{chaser:null}];
let score=[0,0],clock=120,stateT=0,simTime=0,acc=0,lastT=0,rafId=0,cdT=0;
let active=null,activeLock=0,lastKick=null,kickTeam=0,tmpV=null,booted=false;
let camS={x:0,y:12,z:20,lx:0,lz:0,init:false},menuT=0,hudCache={};
const input={jx:0,jy:0,sprint:false,shootHeld:false,shootRel:false,passQ:false,charge:0};
const kb={l:0,r:0,u:0,d:0,s:0};
let style=0,bestStyle=store.get('bstyle',0),inputAC=null,pendingSay=null,bubbleCD=0,lineCD={};
let quality={pr:1,shadows:true,level:0},fpsAcc=0,fpsN=0,fpsTimer=0;
const isTouch=('ontouchstart' in window)||navigator.maxTouchPoints>0;
const U={};
const matCache={};

/* =====================================================================
   AUDIO — pure Web Audio synthesis
   ===================================================================== */
const audio=(function(){
  let ctx=null,master=null,noise=null,on=settings.sound,hornT=rr(6,14);
  function init(){
    if(ctx) return;
    try{
      const AC=window.AudioContext||window.webkitAudioContext; if(!AC) return;
      ctx=new AC(); master=ctx.createGain(); master.gain.value=on?0.5:0; master.connect(ctx.destination);
      const len=ctx.sampleRate*2; noise=ctx.createBuffer(1,len,ctx.sampleRate);
      const d=noise.getChannelData(0); for(let i=0;i<len;i++) d[i]=Math.random()*2-1;
      ambient();
    }catch(e){ctx=null;}
  }
  function resume(){ if(ctx&&ctx.state==='suspended') ctx.resume().catch(()=>{}); }
  function suspend(){ if(ctx&&ctx.state==='running') ctx.suspend().catch(()=>{}); }
  function setOn(v){ on=v; if(master) master.gain.setTargetAtTime(v?0.5:0,ctx.currentTime,0.05); }
  function src(loop){ const s=ctx.createBufferSource(); s.buffer=noise; s.loop=!!loop; return s; }
  function ambient(){
    const s=src(true),bp=ctx.createBiquadFilter(),g=ctx.createGain();
    bp.type='bandpass'; bp.frequency.value=420; bp.Q.value=0.5; g.gain.value=0.04;
    s.connect(bp); bp.connect(g); g.connect(master); s.start();
    const lfo=ctx.createOscillator(),lg=ctx.createGain(); lfo.frequency.value=0.13; lg.gain.value=0.015;
    lfo.connect(lg); lg.connect(g.gain); lfo.start();
  }
  function noiseB(freq,q,type,a,h,r,peak,delay){
    if(!ctx||!on) return; const t=ctx.currentTime+(delay||0);
    const s=src(true),f=ctx.createBiquadFilter(),g=ctx.createGain();
    f.type=type; f.frequency.value=freq; f.Q.value=q;
    g.gain.setValueAtTime(0.0001,t); g.gain.linearRampToValueAtTime(peak,t+a); g.gain.setValueAtTime(peak,t+a+h); g.gain.linearRampToValueAtTime(0.0001,t+a+h+r);
    s.connect(f); f.connect(g); g.connect(master); s.start(t); s.stop(t+a+h+r+0.05);
  }
  function tone(type,f0,f1,dur,peak,delay){
    if(!ctx||!on) return; const t=ctx.currentTime+(delay||0);
    const o=ctx.createOscillator(),g=ctx.createGain(); o.type=type;
    o.frequency.setValueAtTime(f0,t); if(f1) o.frequency.exponentialRampToValueAtTime(f1,t+dur);
    g.gain.setValueAtTime(peak,t); g.gain.exponentialRampToValueAtTime(0.0001,t+dur);
    o.connect(g); g.connect(master); o.start(t); o.stop(t+dur+0.02);
  }
  return {
    init,resume,suspend,setOn,get on(){return on;},
    kick(p){ p=clamp(p,0.15,1); noiseB(900,0.7,'lowpass',0.004,0.02,0.07,0.55*p); tone('sine',150,55,0.11,0.6*p); },
    thud(){ tone('sine',110,50,0.12,0.35); },
    post(){ tone('triangle',620,400,0.35,0.35); tone('square',1250,900,0.2,0.08); },
    whistle(long){
      if(!ctx||!on) return; const t=ctx.currentTime,d=long?0.95:0.42;
      const o=ctx.createOscillator(),m=ctx.createOscillator(),mg=ctx.createGain(),g=ctx.createGain();
      o.type='sine'; o.frequency.value=2650; m.frequency.value=48; mg.gain.value=170; m.connect(mg); mg.connect(o.frequency);
      g.gain.setValueAtTime(0.0001,t); g.gain.linearRampToValueAtTime(0.28,t+0.03); g.gain.setValueAtTime(0.28,t+d-0.05); g.gain.linearRampToValueAtTime(0.0001,t+d);
      o.connect(g); g.connect(master); o.start(t); m.start(t); o.stop(t+d+0.02); m.stop(t+d+0.02);
    },
    cheer(){ noiseB(1000,0.6,'bandpass',0.12,1.4,0.9,0.45); noiseB(2200,0.8,'bandpass',0.2,1.0,0.8,0.12); tone('sawtooth',330,420,1.8,0.04); tone('sawtooth',415,500,1.8,0.035,0.1); },
    groan(){ noiseB(500,0.5,'bandpass',0.1,0.5,0.7,0.3); tone('sawtooth',300,170,1.0,0.05); },
    gasp(){ noiseB(1600,0.7,'bandpass',0.25,0.1,0.35,0.22); },
    horn(){ if(!ctx||!on) return; tone('square',430,430,0.16,0.035); tone('square',340,340,0.28,0.035,0.2); },
    tick(dt){ hornT-=dt; if(hornT<=0){ hornT=rr(9,20); audio.horn(); } }
  };
})();

/* =====================================================================
   LOADER (Three.js from CDN with fallbacks + visible error)
   ===================================================================== */
const CDNS=['https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js',
            'https://cdn.jsdelivr.net/npm/three@0.128.0/build/three.min.js',
            'https://unpkg.com/three@0.128.0/build/three.min.js'];
function setProg(p,t){ $('loadBar').style.width=(p*100)+'%'; if(t) $('loadTxt').textContent=t; }
function showError(msg){ $('loading').classList.add('hidden'); $('errBox').classList.remove('hidden'); $('errMsg').textContent=msg; }
function loadScript(src,ms){
  return new Promise((res,rej)=>{
    const s=document.createElement('script'); let done=false;
    const to=setTimeout(()=>{ if(!done){done=true;rej(new Error('timeout'));} },ms);
    s.onload=()=>{ if(!done){done=true;clearTimeout(to);res();} };
    s.onerror=()=>{ if(!done){done=true;clearTimeout(to);rej(new Error('fail'));} };
    s.src=src; document.head.appendChild(s);
  });
}
const nextFrame=()=>new Promise(r=>requestAnimationFrame(()=>r()));
async function boot(){
  setProg(0.04,'جاري تحميل محرك الـ 3D…');
  let ok=!!window.THREE;
  for(let i=0;i<CDNS.length&&!ok;i++){ try{ await loadScript(CDNS[i],9000); ok=!!window.THREE; }catch(e){} }
  if(!ok){ showError('محرك Three.js ما اتحمّلش. اتأكد إن الإنترنت شغّال (اللعبة محتاجة تحميل مكتبة Three.js مرة واحدة من الـ CDN) وحاول تاني. / Could not load Three.js from the CDN — check your internet connection and retry.'); return; }
  try{ await init(); }catch(e){ console.error(e); showError('حصلت مشكلة أثناء تحميل اللعبة: '+(e&&e.message?e.message:e)); }
}
window.addEventListener('error',e=>{ if(!booted){ console.error(e.error||e.message); } });

/* =====================================================================
   CANVAS / TEXTURE HELPERS
   ===================================================================== */
function cv(w,h){const c=document.createElement('canvas');c.width=w;c.height=h;return c;}
function tex(c,rep){const t=new THREE.CanvasTexture(c);t.anisotropy=4;if(rep){t.wrapS=t.wrapT=THREE.RepeatWrapping;t.repeat.set(rep[0],rep[1]);}return t;}
function M(color,opts){const k=color+(opts?JSON.stringify(opts):'');return matCache[k]||(matCache[k]=new THREE.MeshLambertMaterial(Object.assign({color:color},opts||{})));}
function mk(geo,mat,sx,sy,sz,x,y,z,cast,recv){const m=new THREE.Mesh(geo,mat);m.scale.set(sx,sy,sz);m.position.set(x,y,z);m.castShadow=!!cast;m.receiveShadow=!!recv;return m;}
function scaleUV(geo,sx,sy){const uv=geo.attributes.uv;for(let i=0;i<uv.count;i++)uv.setXY(i,uv.getX(i)*sx,uv.getY(i)*sy);uv.needsUpdate=true;}
function boxUV(geo,w,h,d,tw,th){
  const uv=geo.attributes.uv,dims=[[d,h],[d,h],[w,d],[w,d],[w,h],[w,h]];
  for(let f=0;f<6;f++)for(let i=0;i<4;i++){const k=f*4+i;uv.setXY(k,uv.getX(k)*dims[f][0]/tw,uv.getY(k)*dims[f][1]/th);}
  uv.needsUpdate=true;
}
function initGeo(){
  U.box=new THREE.BoxGeometry(1,1,1); U.sph=new THREE.SphereGeometry(1,8,6); U.cyl=new THREE.CylinderGeometry(1,1,1,10);
  U.pl=new THREE.PlaneGeometry(1,1); U.cap=new THREE.SphereGeometry(1,8,5,0,Math.PI*2,0,Math.PI/2); U.cone=new THREE.ConeGeometry(1,1,8);
}
/* instanced groups: many repeated props in one draw call */
function Inst(geo,mat,cast){this.geo=geo;this.mat=mat;this.l=[];this.cast=cast;}
Inst.prototype.add=function(x,y,z,ry,sx,sy,sz,rx){this.l.push(x,y,z,ry,sx,sy,sz,rx||0);};
Inst.prototype.build=function(parent){
  const n=this.l.length/8; if(!n) return null;
  const im=new THREE.InstancedMesh(this.geo,this.mat,n),o=new THREE.Object3D();
  for(let i=0;i<n;i++){const k=i*8;o.position.set(this.l[k],this.l[k+1],this.l[k+2]);o.rotation.set(this.l[k+7],this.l[k+3],0);o.scale.set(this.l[k+4],this.l[k+5],this.l[k+6]);o.updateMatrix();im.setMatrixAt(i,o.matrix);}
  im.instanceMatrix.needsUpdate=true; im.frustumCulled=false; im.castShadow=!!this.cast; parent.add(im); return im;
};

/* ----- sign texture: real Arabic text via canvas (system font shaping) ----- */
function signTex(text,o){
  const w=o.w||512,h=o.h||128,c=cv(w,h),g=c.getContext('2d');
  g.fillStyle=o.bg; g.fillRect(0,0,w,h);
  if(o.stripe){g.fillStyle=o.stripe;g.fillRect(0,0,w,12);g.fillRect(0,h-12,w,12);}
  g.strokeStyle=o.border||o.fg; g.lineWidth=7; g.strokeRect(9,9,w-18,h-18);
  for(let i=0;i<40;i++){g.fillStyle='rgba(0,0,0,'+(rnd()*0.08)+')';g.fillRect(rnd()*w,rnd()*h,rnd()*40,rnd()*10);}
  try{g.direction='rtl';}catch(e){}
  g.textAlign='center'; g.textBaseline='middle';
  let size=o.size||74; const fam=o.font||FONT;
  do{ g.font='bold '+size+'px '+fam; size-=4; }while(g.measureText(text).width>w-56&&size>20);
  if(o.shadow){g.fillStyle=o.shadow;g.fillText(text,w/2+3,h/2+5);}
  g.fillStyle=o.fg; g.fillText(text,w/2,h/2+3);
  return tex(c);
}
function signMesh(text,o,sw,sh){
  return new THREE.Mesh(new THREE.PlaneGeometry(sw,sh),new THREE.MeshBasicMaterial({map:signTex(text,o)}));
}
const SIGNS={
  kiosk:['كشك عم سيد',{bg:'#2e6b3f',fg:'#fff3b0',border:'#fff3b0',shadow:'#12301b',font:'"Noto Kufi Arabic","Droid Arabic Kufi",Tahoma,Arial,sans-serif'}],
  ful:['فول وطعمية الحاج رجب',{bg:'#f2c230',fg:'#7a1410',border:'#7a1410',stripe:'#d9382b',size:64}],
  barber:['حلاقة أبو شريف',{bg:'#1d4f8f',fg:'#fff',border:'#ffd23f',shadow:'#0a2344',font:'"Noto Naskh Arabic","Droid Arabic Naskh",Tahoma,serif'}],
  street:['شارع العشرين',{bg:'#1a5fb4',fg:'#fff',border:'#fff',w:512,h:128}],
  nopark:['ممنوع ركن السيارات',{bg:'#ffffff',fg:'#c1121f',border:'#c1121f',stripe:'#c1121f',size:62}],
  pharm:['صيدلية الأمل',{bg:'#1f8a4c',fg:'#fff',border:'#fff',shadow:'#0b3f22'}],
  juice:['عصير قصب الريس',{bg:'#7bc043',fg:'#2c2c00',border:'#2c2c00'}],
  books:['مكتبة النور',{bg:'#8a2b2b',fg:'#ffe9b0',border:'#ffe9b0',font:'"Noto Naskh Arabic",Tahoma,serif'}],
  garage:['ورشة الأسطى حسن',{bg:'#3b3b3b',fg:'#ffd23f',border:'#ffd23f',stripe:'#ffd23f'}],
  market:['سوبر ماركت السلام',{bg:'#d93a3a',fg:'#fff',border:'#fff',size:64}],
  mobile:['موبايلات الشروق',{bg:'#6a3fb5',fg:'#fff',border:'#ffd23f'}]
};
function shopTex(kind){
  const c=cv(128,128),g=c.getContext('2d');
  g.fillStyle='#2a211a'; g.fillRect(0,0,128,128);
  const grad=g.createLinearGradient(0,0,0,128); grad.addColorStop(0,'rgba(255,220,150,.35)'); grad.addColorStop(1,'rgba(0,0,0,.2)'); g.fillStyle=grad; g.fillRect(0,0,128,128);
  const cols=['#d9382b','#f2c230','#2a9d8f','#e76f51','#4361ee','#8ac926','#fff'];
  if(kind==='barber'){ g.fillStyle='#b8c7d1'; g.fillRect(14,14,44,70); g.fillRect(70,14,44,70); g.fillStyle='#222'; g.fillRect(14,90,100,24); }
  else if(kind==='ful'){ g.fillStyle='#8a8a8a'; g.fillRect(10,60,108,12); g.fillStyle='#d9a441'; for(let i=0;i<5;i++){g.beginPath();g.arc(24+i*20,52,9,0,6.3);g.fill();} g.fillStyle='#fff'; g.fillRect(10,76,108,40); }
  else { for(let y=20;y<110;y+=26){ g.fillStyle='#6b4a2f'; g.fillRect(8,y+16,112,5); for(let x=12;x<112;x+=14){ g.fillStyle=cols[(rnd()*cols.length)|0]; g.fillRect(x,y,10,16);} } }
  return tex(c);
}

/* ----- pitch texture: sandy dirt, worn patches, footprints, chalk ----- */
function makePitchTex(){
  const W=960,H=1440,S=48,c=cv(W,H),g=c.getContext('2d');
  g.fillStyle='#d6b67f'; g.fillRect(26,26,W-52,H-52);
  // irregular edges
  for(let i=0;i<420;i++){
    const side=(rnd()*4)|0; let x,y;
    if(side===0){x=rnd()*W;y=24+gauss()*14;}else if(side===1){x=rnd()*W;y=H-24+gauss()*14;}else if(side===2){x=24+gauss()*14;y=rnd()*H;}else{x=W-24+gauss()*14;y=rnd()*H;}
    g.globalCompositeOperation=rnd()<0.45?'destination-out':'source-over'; g.fillStyle='#d6b67f';
    g.beginPath(); g.arc(x,y,6+rnd()*26,0,6.3); g.fill();
  }
  g.globalCompositeOperation='source-atop';
  const blob=(x,y,r,col)=>{const gr=g.createRadialGradient(x,y,0,x,y,r);gr.addColorStop(0,col);gr.addColorStop(1,'rgba(0,0,0,0)');g.fillStyle=gr;g.fillRect(x-r,y-r,r*2,r*2);};
  for(let i=0;i<26;i++) blob(rnd()*W,rnd()*H,60+rnd()*150,rnd()<0.5?'rgba(150,108,62,.28)':'rgba(240,222,176,.30)');
  blob(W/2,H/2,190,'rgba(130,92,52,.30)'); blob(W/2,90,170,'rgba(125,88,50,.38)'); blob(W/2,H-90,170,'rgba(125,88,50,.38)');
  for(let i=0;i<9000;i++){ g.fillStyle=rnd()<0.5?'rgba(110,78,44,'+(0.05+rnd()*0.18)+')':'rgba(250,236,200,'+(0.05+rnd()*0.16)+')'; const s=1+rnd()*3; g.fillRect(rnd()*W,rnd()*H,s,s); }
  for(let i=0;i<70;i++){ g.fillStyle='rgba(90,66,40,.5)'; g.beginPath(); g.arc(rnd()*W,rnd()*H,1+rnd()*2.4,0,6.3); g.fill(); }
  // old footprints
  for(let i=0;i<130;i++){ const x=100+rnd()*(W-200),y=100+rnd()*(H-200),a=rnd()*6.3; g.save(); g.translate(x,y); g.rotate(a); g.fillStyle='rgba(95,68,40,.17)'; g.beginPath(); g.ellipse(-4,0,3.2,6.5,0,0,6.3); g.fill(); g.beginPath(); g.ellipse(5,9,3.2,6.5,0,0,6.3); g.fill(); g.restore(); }
  g.strokeStyle='rgba(62,45,28,.55)'; g.lineWidth=1.6;
  for(let i=0;i<14;i++){ let x=rnd()*W,y=rnd()*H; g.beginPath(); g.moveTo(x,y); for(let k=0;k<10;k++){ x+=gauss()*26; y+=gauss()*26; g.lineTo(x,y);} g.stroke(); }
  g.globalCompositeOperation='source-over';
  // chalk lines
  const X=x=>(x+10)*S, Z=z=>(z+15)*S;
  g.lineCap='round';
  function chalk(x1,y1,x2,y2){
    const len=Math.hypot(x2-x1,y2-y1),n=Math.ceil(len/5);
    for(let i=0;i<n;i++){ if(rnd()<0.035) continue; const t=i/n,t2=(i+1)/n;
      g.strokeStyle='rgba(252,250,242,'+(0.72+rnd()*0.26)+')'; g.lineWidth=5+rnd()*2;
      g.beginPath(); g.moveTo(x1+(x2-x1)*t+(rnd()-.5)*1.4,y1+(y2-y1)*t+(rnd()-.5)*1.4); g.lineTo(x1+(x2-x1)*t2,y1+(y2-y1)*t2); g.stroke(); }
  }
  chalk(X(-PW),Z(-PL),X(PW),Z(-PL)); chalk(X(PW),Z(-PL),X(PW),Z(PL)); chalk(X(PW),Z(PL),X(-PW),Z(PL)); chalk(X(-PW),Z(PL),X(-PW),Z(-PL));
  chalk(X(-PW),Z(0),X(PW),Z(0));
  let px=X(2.2),py=Z(0); for(let a=0.2;a<=6.5;a+=0.2){ const nx=X(Math.cos(a)*2.2),ny=Z(Math.sin(a)*2.2); chalk(px,py,nx,ny); px=nx;py=ny; }
  for(const s of [-1,1]){ const zb=s*PL, zi=s*(PL-2.8); chalk(X(-3.4),Z(zb),X(-3.4),Z(zi)); chalk(X(-3.4),Z(zi),X(3.4),Z(zi)); chalk(X(3.4),Z(zi),X(3.4),Z(zb)); }
  g.fillStyle='rgba(252,250,242,.9)'; g.beginPath(); g.arc(X(0),Z(0),6,0,6.3); g.fill();
  const t=tex(c); t.anisotropy=8; return t;
}
function makeAsphaltTex(){
  const c=cv(512,512),g=c.getContext('2d');
  g.fillStyle='#7d7064'; g.fillRect(0,0,512,512);
  for(let i=0;i<30;i++){ g.fillStyle='rgba('+(rnd()<0.5?'60,50,42':'170,150,120')+','+(0.05+rnd()*0.1)+')'; g.fillRect(rnd()*512,rnd()*512,30+rnd()*120,20+rnd()*80); }
  for(let i=0;i<6000;i++){ g.fillStyle=rnd()<0.5?'rgba(40,34,28,'+(rnd()*0.3)+')':'rgba(220,200,160,'+(rnd()*0.25)+')'; g.fillRect(rnd()*512,rnd()*512,1+rnd()*2,1+rnd()*2); }
  g.strokeStyle='rgba(30,25,20,.45)'; g.lineWidth=1.3;
  for(let i=0;i<8;i++){ let x=rnd()*512,y=rnd()*512; g.beginPath(); g.moveTo(x,y); for(let k=0;k<8;k++){x+=gauss()*22;y+=gauss()*22;g.lineTo(x,y);} g.stroke(); }
  return tex(c,[14,16]);
}
function makeSky(){
  const c=cv(4,256),g=c.getContext('2d'),gr=g.createLinearGradient(0,0,0,256);
  gr.addColorStop(0,'#2b4a7a'); gr.addColorStop(0.4,'#7f8fb0'); gr.addColorStop(0.75,'#e0976a'); gr.addColorStop(1,'#f2b36a');
  g.fillStyle=gr; g.fillRect(0,0,4,256); return new THREE.CanvasTexture(c);
}
const FAC_COLORS=['#e6d6b2','#d9c4a0','#e4c6bc','#c8d4c0','#e8dca6','#d2c9b8'];
function makeFacadeTex(base){
  const c=cv(256,256),g=c.getContext('2d');
  g.fillStyle=base; g.fillRect(0,0,256,256);
  for(let i=0;i<90;i++){ g.fillStyle='rgba('+(rnd()<0.5?'90,70,50':'255,255,255')+','+(rnd()*0.07)+')'; g.fillRect(rnd()*256,rnd()*256,10+rnd()*50,6+rnd()*40); }
  for(let col=0;col<2;col++){
    const x0=col*128+34,y0=58,w=60,h=128,kind=(rnd()*4)|0;
    g.fillStyle='rgba(70,52,38,.38)'; g.fillRect(x0-6,y0-6,w+12,h+14);
    if(kind===0){
      g.fillStyle=['#3e6b4a','#6b4a2f','#2f5f7a','#5b6b3a'][(rnd()*4)|0]; g.fillRect(x0,y0,w,h);
      g.strokeStyle='rgba(0,0,0,.35)'; g.lineWidth=2;
      for(let y=y0+6;y<y0+h;y+=8){g.beginPath();g.moveTo(x0,y);g.lineTo(x0+w,y);g.stroke();}
      g.beginPath();g.moveTo(x0+w/2,y0);g.lineTo(x0+w/2,y0+h);g.stroke();
    }else if(kind===1){
      g.fillStyle='#27323c'; g.fillRect(x0,y0,w,h); g.fillStyle='rgba(255,255,255,.16)'; g.fillRect(x0+4,y0+4,w/2-6,h-8);
      g.fillStyle=['#e6d5c3','#d9a7a0','#cfd8e3'][(rnd()*3)|0]; g.fillRect(x0,y0,w,h*0.38);
    }else if(kind===2){
      g.fillStyle='#202a33'; g.fillRect(x0,y0,w,h); g.fillStyle='#4d3a28'; g.fillRect(x0,y0,14,h); g.fillRect(x0+w-14,y0,14,h);
      g.fillStyle='rgba(255,230,160,.35)'; g.fillRect(x0+16,y0+10,w-32,h-20);
    }else{
      g.fillStyle='#e9c46a'; g.fillRect(x0,y0,w,h); g.fillStyle='rgba(40,28,10,.55)'; g.fillRect(x0+4,y0+h*0.55,w-8,h*0.45);
    }
    g.strokeStyle='#f4efe4'; g.lineWidth=3; g.strokeRect(x0,y0,w,h); g.beginPath(); g.moveTo(x0+w/2,y0); g.lineTo(x0+w/2,y0+h); g.stroke();
    g.fillStyle='rgba(60,40,28,.25)'; g.fillRect(x0-4,y0+h+2,w+8,5);
    g.fillStyle='rgba(60,45,35,.14)'; g.fillRect(x0+3,y0+h+7,w-6,26+rnd()*16);
  }
  g.fillStyle='rgba(0,0,0,.22)'; g.fillRect(0,250,256,6); g.fillStyle='rgba(255,255,255,.22)'; g.fillRect(0,247,256,3);
  const t=tex(c,null); t.wrapS=t.wrapT=THREE.RepeatWrapping; return t;
}

/* =====================================================================
   WORLD
   ===================================================================== */
let facMats=[],roofMat,cableGroup;
function wallOf(cx,cz,len,nx,nz){return {cx,cz,len,nx,nz,tx:Math.abs(nz),tz:Math.abs(nx),ry:Math.atan2(nx,nz)};}
function wp(w,u,off){return [w.cx+w.tx*u+w.nx*off, w.cz+w.tz*u+w.nz*off];}
function placeAt(obj,w,u,y,off){const p=wp(w,u,off);obj.position.set(p[0],y,p[1]);obj.rotation.y=w.ry;return obj;}

const InstSet={};
function initInst(){
  InstSet.slab=new Inst(U.box,M(0xa89c8a),false); InstSet.rail=new Inst(U.box,M(0x2a2622),false);
  InstSet.ac=new Inst(U.box,M(0xf0efe8),false); InstSet.acD=new Inst(U.box,M(0x555555),false);
  InstSet.tank=new Inst(U.cyl,M(0x1c1c1c),false); InstSet.stand=new Inst(U.box,M(0x8d8577),false);
  InstSet.dish=new Inst(U.cap,new THREE.MeshLambertMaterial({color:0xcfd2d4,side:THREE.DoubleSide}),false);
  InstSet.rod=new Inst(U.cyl,M(0x333333),false); InstSet.cloth=[];
  [0xffffff,0xf4a6b8,0x5ab0f0,0xffd23f,0xe5533d].forEach(c=>InstSet.cloth.push(new Inst(U.pl,new THREE.MeshLambertMaterial({color:c,side:THREE.DoubleSide}),false)));
}
function buildBuilding(cx,cz,len,nx,nz,D,floors,fi,gcol,opts){
  opts=opts||{};
  const w=wallOf(cx,cz,len,nx,nz), sx=nx?D:len, sz=nx?len:D, gh=3.4, uh=floors*3;
  const bx=cx-nx*D/2, bz=cz-nz*D/2;
  const gm=mk(U.box,M(gcol),sx,gh,sz,bx,gh/2,bz,false,true); scene.add(gm);
  const geo=new THREE.BoxGeometry(sx,uh,sz); boxUV(geo,sx,uh,sz,4,3);
  const fm=facMats[fi%facMats.length];
  const um=new THREE.Mesh(geo,[fm,fm,roofMat,roofMat,fm,fm]); um.position.set(bx,gh+uh/2,bz); scene.add(um);
  scene.add(mk(U.box,M(0xb9ad98),sx+0.3,0.25,sz+0.3,bx,gh+uh+0.12,bz));
  if(opts.far) return w;
  // balconies, AC units, laundry on upper floors (facing wall)
  const n=Math.floor(len/2);
  for(let f=1;f<=floors;f++){
    const base=gh+(f-1)*3;
    for(let k=0;k<n;k++){
      const u=-len/2+1+2*k, r=rnd(), p=wp(w,u,0);
      if(r<0.24){
        const off=0.46, pp=wp(w,u,off);
        InstSet.slab.add(pp[0],base+0.72,pp[1],w.ry,1.7,0.1,0.9);
        const fr=wp(w,u,0.9); InstSet.rail.add(fr[0],base+1.2,fr[1],w.ry,1.7,0.9,0.04);
        for(const sd of [-0.83,0.83]){ const sp=wp(w,u+sd,off); InstSet.rail.add(sp[0],base+1.2,sp[1],w.ry,0.04,0.9,0.9); }
        if(rnd()<0.6){ // hanging laundry from balcony rail
          const ci=(rnd()*InstSet.cloth.length)|0;
          for(let q=0;q<3;q++){ const cp=wp(w,u-0.55+q*0.55,0.95); InstSet.cloth[(ci+q)%InstSet.cloth.length].add(cp[0],base+0.95,cp[1],w.ry,0.42,0.6,1); }
        }
      }else if(r<0.42){
        const ap=wp(w,u+0.95,0.2); InstSet.ac.add(ap[0],base+0.55,ap[1],w.ry,0.72,0.5,0.36);
        const gp=wp(w,u+0.95,0.39); InstSet.acD.add(gp[0],base+0.55,gp[1],w.ry,0.5,0.36,0.03);
      }
    }
  }
  // a few animated clotheslines near the pitch (individual meshes)
  if(opts.line){
    for(let i=0;i<opts.line;i++){
      const f=1+((rnd()*Math.min(floors,4))|0), u=rr(-len/2+3,len/2-3), base=gh+(f-1)*3+1.6;
      const cols=[0xffffff,0xf4a6b8,0x5ab0f0,0xffd23f,0xe5533d];
      for(let q=0;q<3;q++){
        const m=new THREE.Mesh(U.pl,new THREE.MeshLambertMaterial({color:cols[(rnd()*cols.length)|0],side:THREE.DoubleSide}));
        m.scale.set(0.5,0.7,1); const pp=wp(w,u+q*0.7,0.5); m.position.set(pp[0],base,pp[1]); m.rotation.y=w.ry; m.userData.ph=rnd()*6; m.userData.by=m.rotation.y; scene.add(m); laundry.push(m);
      }
    }
  }
  // rooftop
  const topY=gh+uh+0.25, nt=1+((rnd()*2)|0);
  for(let i=0;i<nt;i++){
    const ox=rr(-sx/2+1.2,sx/2-1.2), oz=rr(-sz/2+1.2,sz/2-1.2);
    InstSet.stand.add(bx+ox,topY+0.2,bz+oz,0,1.3,0.4,1.3); InstSet.tank.add(bx+ox,topY+0.4+0.55,bz+oz,0,0.55,1.1,0.55);
  }
  for(let i=0;i<2;i++){
    const ox=rr(-sx/2+1,sx/2-1), oz=rr(-sz/2+1,sz/2-1);
    InstSet.dish.add(bx+ox,topY+1.3,bz+oz,rr(0,6),0.42,0.42,0.42,-1.1); InstSet.rod.add(bx+ox,topY+0.65,bz+oz,0,0.03,1.3,0.03);
  }
  InstSet.rod.add(bx+rr(-sx/3,sx/3),topY+1.4,bz+rr(-sz/3,sz/3),0,0.025,2.8,0.025);
  return w;
}
/* ground-floor shop */
function addShop(w,u,width,key,interior,awnCol){
  const grp=new THREE.Group();
  const door=new THREE.Mesh(new THREE.PlaneGeometry(width*0.78,2.3),new THREE.MeshBasicMaterial({map:shopTex(interior)}));
  placeAt(door,w,u,1.2,0.04); scene.add(door);
  const aw=mk(U.box,M(awnCol),width*0.9,0.07,1.0,0,0,0); aw.rotation.x=0.32; placeAt(aw,w,u,2.55,0.55); aw.rotation.x=0.32; scene.add(aw);
  const sg=SIGNS[key]; const sm=signMesh(sg[0],sg[1],Math.min(4.2,width*1.05),1.05); placeAt(sm,w,u,3.0,0.06); scene.add(sm);
  // crates / stools out front
  for(let i=0;i<2;i++){ const cr=mk(U.box,M([0xc0392b,0x2e86c1,0xd4ac0d,0x27ae60][(rnd()*4)|0]),0.5,0.4,0.4,0,0,0,true); placeAt(cr,w,u+(i?0.7:-0.8),0.2,0.95+rnd()*0.3); cr.rotation.y+=rr(-0.4,0.4); scene.add(cr); }
}
function buildEnvironment(){
  facMats=FAC_COLORS.map(c=>new THREE.MeshLambertMaterial({map:makeFacadeTex(c)}));
  roofMat=M(0x9a8f80); initInst();
  const GC=['#d8c9a8','#cdb89a','#e3cbc0','#c7cfbf','#dccd9c'];
  // left side (face +x) and right side (face -x). lengths are even so windows align with texture tiles
  const L=[[-30,12,0],[-14.5,12,2],[0.5,12,4],[15.5,12,1],[30.5,12,3]];
  const Rr=[[-31,10,5],[-17,10,1],[-2.5,12,3],[12.5,12,0],[27.5,16,2]];
  L.forEach((s,i)=>{ const fl=4+((rnd()*3)|0); buildBuilding(-13.2,s[0],s[1],1,0,8,fl,s[2],GC[i%5],{line:2}); });
  Rr.forEach((s,i)=>{ const fl=4+((rnd()*3)|0); buildBuilding(13.2,s[0],s[1],-1,0,8,fl,s[2],GC[(i+2)%5],{line:2}); });
  // alley end walls + far blocks
  buildBuilding(-30,0,90,1,0,8,6,5,'#bfae94',{far:true}); buildBuilding(30,0,90,-1,0,8,6,4,'#bfae94',{far:true});
  // end buildings behind the opponent goal (face +z), street gap in the middle
  const wN1=buildBuilding(-7.6,-26,12,0,1,8,5,2,GC[1],{line:1}), wN2=buildBuilding(7.6,-26,12,0,1,8,5,0,GC[3],{line:1});
  buildBuilding(0,-44,60,0,1,8,6,3,'#bfae94',{far:true}); buildBuilding(0,46,60,0,-1,8,6,1,'#bfae94',{far:true});
  const wS1=buildBuilding(-16,40,30,0,-1,8,5,5,GC[0],{far:true});
  for(const k of Object.keys(InstSet)){ const v=InstSet[k]; if(Array.isArray(v)) v.forEach(i=>i.build(scene)); else v.build(scene); }
  // shops (left wall: x=-13.2, right wall: x=+13.2)
  const wl=(z0,len)=>wallOf(-13.2,z0,len,1,0), wr=(z0,len)=>wallOf(13.2,z0,len,-1,0);
  addShop(wl(-14.5,12),-3,3.8,'barber','barber',0xd9382b);
  addShop(wl(-14.5,12),3,3.8,'books','grocery',0x2a9d8f);
  addShop(wl(0.5,12),-3,3.8,'ful','ful',0xf2c230);
  addShop(wl(0.5,12),3,3.8,'pharm','grocery',0x1f8a4c);
  addShop(wl(15.5,12),0,4.2,'juice','grocery',0x7bc043);
  addShop(wl(-30,12),0,4.2,'garage','grocery',0x555555);
  addShop(wr(-17,10),-2,3.8,'market','grocery',0xd93a3a);
  addShop(wr(-2.5,12),-3,3.8,'mobile','grocery',0x6a3fb5);
  addShop(wr(-2.5,12),3,3.8,'ful','ful',0xe76f51);
  addShop(wr(12.5,12),0,4.2,'barber','barber',0x2e86c1);
  addShop(wallOf(-7.6,-26,12,0,1),0,4.2,'market','grocery',0xe76f51);
  addShop(wallOf(7.6,-26,12,0,1),0,4.2,'juice','grocery',0xf2c230);
  // street-name plate + no-parking sign
  const sp=signMesh(SIGNS.street[0],SIGNS.street[1],2.8,0.7); placeAt(sp,wallOf(-7.6,-26,12,0,1),-4.2,4.6,0.08); scene.add(sp);
  const np=signMesh(SIGNS.nopark[0],SIGNS.nopark[1],2.6,0.75); placeAt(np,wl(-14.5,12),-4.7,2.0,0.05); scene.add(np);
  const np2=signMesh(SIGNS.nopark[0],SIGNS.nopark[1],2.6,0.75); placeAt(np2,wr(12.5,12),3.7,2.0,0.05); scene.add(np2);
  // kiosk
  buildKiosk();
  // sidewalks
  for(const s of [-1,1]) scene.add(mk(U.box,M(0xa39a8a),1.3,0.12,100,s*12.55,0.06,0,false,true));
  // cables across the street
  cableGroup=new THREE.Group(); const lm=new THREE.LineBasicMaterial({color:0x1a1a1a});
  [[-14,8.2,10],[-6,9.4,12],[3,8.8,9],[14,9.6,11],[22,8.4,10]].forEach(c=>{
    const pts=[]; for(let i=0;i<=14;i++){ const t=i/14; pts.push(new THREE.Vector3(lerp(-12.8,12.8,t)+rr(-0.0,0.0),c[1]-Math.sin(t*Math.PI)*0.9,c[0])); }
    cableGroup.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts),lm));
  });
  scene.add(cableGroup);
  // distant skyline (hazy)
  const hz=M(0xc9aa8c);
  for(let i=0;i<26;i++){ const a=i/26*Math.PI*2, d=rr(78,96), h=rr(14,34); const b=mk(U.box,hz,rr(6,12),h,rr(6,12),Math.sin(a)*d,h/2,-Math.cos(a)*d); scene.add(b); }
  for(const a of [0.5,3.9]){ const d=88; const x=Math.sin(a)*d,z=-Math.cos(a)*d; scene.add(mk(U.cyl,hz,1.3,38,1.3,x,19,z)); scene.add(mk(U.cone,hz,2.0,7,2.0,x,41.5,z)); }
}
function buildKiosk(){
  const g=new THREE.Group(), wood=M(0x4f7f5c);
  g.add(mk(U.box,wood,1.7,2.3,1.7,0,1.15,0,true,true));
  g.add(mk(U.box,M(0x2f4f38),2.1,0.12,2.0,0,2.36,0.12,true));
  const win=new THREE.Mesh(new THREE.PlaneGeometry(1.2,0.9),new THREE.MeshBasicMaterial({map:shopTex('grocery')})); win.position.set(0,1.35,0.86); g.add(win);
  g.add(mk(U.box,M(0x8a6a3a),1.5,0.08,0.5,0,0.95,0.98,true));
  const aw=mk(U.box,M(0xd9382b),1.9,0.06,0.8,0,2.0,1.15); aw.rotation.x=0.35; g.add(aw);
  const sg=SIGNS.kiosk, sm=signMesh(sg[0],sg[1],1.9,0.55); sm.position.set(0,2.62,0.95); g.add(sm);
  for(let i=0;i<2;i++) g.add(mk(U.box,M(0x2e86c1),0.4,0.45,0.4,-0.5+i*0.9,0.22,1.7,true));
  g.position.set(12.1,0,-9.4); g.rotation.y=-Math.PI/2; scene.add(g);
}
function makeCar(o){
  const g=new THREE.Group(),body=M(o.color),glass=M(0x25313b),dark=M(0x141414),chrome=M(0xb6b6b6);
  g.add(mk(U.box,body,o.w,o.bh,o.len,0,o.by+o.bh/2,0,true));
  g.add(mk(U.box,glass,o.w*0.96,o.ch,o.cl,0,o.by+o.bh+o.ch/2,o.co,true));
  g.add(mk(U.box,body,o.w*0.99,0.07,o.cl*0.97,0,o.by+o.bh+o.ch+0.03,o.co,true));
  for(const sx of [-1,1])for(const sz of [-1,1]){const wh=mk(U.cyl,dark,0.32,0.24,0.32,sx*(o.w/2-0.02),0.32,sz*(o.len/2-0.8),true);wh.rotation.z=Math.PI/2;g.add(wh);}
  for(const sx of [-1,1]){ g.add(mk(U.box,M(0xfff2b0),0.26,0.14,0.05,sx*(o.w/2-0.3),o.by+0.38,o.len/2)); g.add(mk(U.box,M(0xc1121f),0.26,0.12,0.05,sx*(o.w/2-0.3),o.by+0.38,-o.len/2)); }
  g.add(mk(U.box,chrome,o.w*0.99,0.1,0.1,0,o.by+0.1,o.len/2+0.03)); g.add(mk(U.box,chrome,o.w*0.99,0.1,0.1,0,o.by+0.1,-o.len/2-0.03));
  if(o.rust) for(let i=0;i<4;i++) g.add(mk(U.box,M(0x7a4a2a),0.35,0.18,0.02,(i%2?1:-1)*(o.w/2+0.005),o.by+0.2+rnd()*0.2,rr(-1.3,1.3)));
  return g;
}
function makeBus(){
  const g=new THREE.Group(),body=M(0xf2f2ee),glass=M(0x25313b),dark=M(0x141414);
  g.add(mk(U.box,body,1.9,1.55,4.5,0,0.45+0.78,0,true));
  g.add(mk(U.box,M(0x1f6fd1),1.92,0.18,4.52,0,1.0,0));
  for(const s of [-1,1]) g.add(mk(U.box,glass,0.02,0.55,3.2,s*0.96,1.78,-0.2));
  g.add(mk(U.box,glass,1.5,0.7,0.03,0,1.7,2.26)); g.add(mk(U.box,M(0xdcdcd8),1.9,0.08,4.5,0,2.28,0,true));
  for(const sx of [-1,1])for(const sz of [-1,1]){const wh=mk(U.cyl,dark,0.34,0.26,0.34,sx*0.92,0.34,sz*1.5,true);wh.rotation.z=Math.PI/2;g.add(wh);}
  for(const sx of [-1,1]){ g.add(mk(U.box,M(0xfff2b0),0.26,0.15,0.05,sx*0.6,0.75,2.26)); g.add(mk(U.box,M(0xc1121f),0.26,0.14,0.05,sx*0.7,0.8,-2.26)); }
  g.add(mk(U.box,M(0xb6b6b6),1.9,0.1,0.1,0,0.55,2.28));
  return g;
}
function buildCars(){
  const a=makeCar({color:0xd7c9a0,w:1.7,len:4.0,bh:0.6,by:0.35,ch:0.5,cl:2.0,co:-0.1}); a.position.set(-10.4,0,-5.5); scene.add(a);
  const b=makeBus(); b.position.set(10.4,0,2.5); b.rotation.y=Math.PI; scene.add(b);
  const c=makeCar({color:0x5d7fa0,w:1.65,len:3.7,bh:0.7,by:0.35,ch:0.55,cl:2.1,co:-0.1,rust:true}); c.position.set(-10.4,0,8.2); c.rotation.y=Math.PI; scene.add(c);
}
function buildGoals(){
  const metal=M(0xc8ccd0);
  function netMat(rx,ry){const c=cv(64,64),g=c.getContext('2d');g.strokeStyle='rgba(255,255,255,.75)';g.lineWidth=2;g.strokeRect(0,0,64,64);const t=tex(c,[rx,ry]);return new THREE.MeshBasicMaterial({map:t,transparent:true,side:THREE.DoubleSide,depthWrite:false,opacity:0.85});}
  const nets=[netMat(8,4),netMat(8,3),netMat(3,4)];
  for(const s of [1,-1]){
    const g=new THREE.Group();
    for(const x of [-GW,GW]){ g.add(mk(U.cyl,metal,0.06,GH,0.06,x,GH/2,0,true)); g.add(mk(U.cyl,metal,0.05,1.5,0.05,x,0.0+GH*0.35,1.5,true)); g.children[g.children.length-1].scale.set(0.05,1.4,0.05); g.children[g.children.length-1].position.set(x,0.7,1.5);
      const diag=mk(U.cyl,metal,0.035,1.95,0.035,x,GH*0.5,0.75,true); diag.rotation.x=Math.atan2(1.5,1.4)-0; diag.rotation.x=1.0; diag.position.set(x,1.0,0.75); g.add(diag); }
    const bar=mk(U.cyl,metal,0.06,GW*2,0.06,0,GH,0,true); bar.rotation.z=Math.PI/2; g.add(bar);
    const bar2=mk(U.cyl,metal,0.05,GW*2,0.05,0,1.4,1.5,true); bar2.rotation.z=Math.PI/2; g.add(bar2);
    const back=new THREE.Mesh(U.pl,nets[0]); back.scale.set(GW*2,1.4,1); back.position.set(0,0.7,1.5); g.add(back);
    const top=new THREE.Mesh(U.pl,nets[1]); top.scale.set(GW*2,1.58,1); top.rotation.x=-Math.PI/2+0.38; top.position.set(0,1.7,0.75); g.add(top);
    for(const x of [-GW,GW]){ const sd=new THREE.Mesh(U.pl,nets[2]); sd.scale.set(1.5,1.7,1); sd.rotation.y=Math.PI/2; sd.position.set(x,0.85,0.75); g.add(sd); }
    g.position.set(0,0,s*PL); g.rotation.y=s>0?0:Math.PI; scene.add(g);
  }
  // corner cones
  for(const x of [-PW,PW])for(const z of [-PL,PL]) scene.add(mk(U.cone,M(0xff7a1a),0.16,0.4,0.16,x,0.2,z,true));
}

/* =====================================================================
   CHARACTERS (procedural low-poly articulated)
   ===================================================================== */
const SKIN=[0xf0c8a0,0xe0b080,0xc68c5c,0xa8704a,0x8a5a3a,0xd9a574];
const shirtCache={};
function shirtMat(c1,style,c2){
  const k=c1+'|'+style+'|'+c2; if(shirtCache[k]) return shirtCache[k];
  let m;
  if(!style||style==='plain') m=new THREE.MeshLambertMaterial({color:c1});
  else{
    const c=cv(64,64),g=c.getContext('2d'); g.fillStyle=c1; g.fillRect(0,0,64,64); g.fillStyle=c2;
    if(style==='stripeV'){for(let x=0;x<64;x+=16)g.fillRect(x,0,8,64);}else{for(let y=0;y<64;y+=16)g.fillRect(0,y,64,8);}
    m=new THREE.MeshLambertMaterial({map:new THREE.CanvasTexture(c)});
  }
  shirtCache[k]=m; return m;
}
const cylCache={};
function cylG(rt,rb,h,seg){const k=rt+'|'+rb+'|'+h+'|'+(seg||12);return cylCache[k]||(cylCache[k]=new THREE.CylinderGeometry(rt,rb,h,seg||12));}
function createChar(o){
  /* athletic ~1.8m body: separate hips + chest groups (spine twist/lean), tapered muscular limbs,
     knee/elbow joints, neck + head that can look at the ball. Full detail for players, lite for crowd. */
  const root=new THREE.Group(),body=new THREE.Group(),hips=new THREE.Group(),chest=new THREE.Group();
  root.add(body); body.add(hips); body.add(chest); hips.position.y=0.93; chest.position.y=1.0;
  if(!U.sph14) U.sph14=new THREE.SphereGeometry(1,14,10);
  const S=U.sph14,lite=o.cast===false,cast=!lite,bw=o.bw||1;
  const skin=M(o.skin),shirt=shirtMat(o.shirt,o.style,o.shirt2),shorts=M(o.shorts),shoe=M(o.shoe),sole=M(0xf2f2f2),dark=M(0x16100c),hair=M(o.hair),sockM=M(o.sock||0xf0f0f0);
  const sg=lite?9:12;
  // --- hips / pelvis
  hips.add(mk(cylG(0.15,0.18,0.22,sg),shorts,1.2*bw,1,0.72,0,0.03,0,cast));
  // --- chest group: abdomen, chest, traps, neck, shoulders, head
  chest.add(mk(cylG(0.16,0.155,0.2,sg),shirt,1.12*bw,1,0.62,0,0.08,0,cast));
  chest.add(mk(cylG(0.215,0.165,0.34,sg),shirt,1.17*bw,1,0.64,0,0.3,0,cast));
  chest.add(mk(cylG(0.05,0.058,0.13,10),skin,1,1,1,0,0.55,0,cast));
  if(!lite){
    chest.add(mk(S,shirt,0.17*bw,0.04,0.09,0,0.485,-0.005,cast));
    for(const sd of [-1,1]) chest.add(mk(S,shirt,0.072,0.078,0.072,sd*0.238*bw,0.455,0,cast));
  }
  const head=new THREE.Group(); head.position.set(0,0.68,0); chest.add(head);
  head.add(mk(S,skin,0.106,0.128,0.115,0,0,0,cast));
  if(!lite){
    head.add(mk(S,skin,0.083,0.074,0.096,0,-0.07,0.02,cast));       // jaw
    head.add(mk(S,skin,0.03,0.022,0.03,0,-0.115,0.07,cast));        // chin
    head.add(mk(S,skin,0.02,0.027,0.026,0,-0.015,0.117));           // nose
    for(const sd of [-1,1]){
      head.add(mk(S,skin,0.016,0.032,0.024,sd*0.106,0,0));           // ears
      head.add(mk(S,M(0xf4efe8),0.015,0.01,0.008,sd*0.04,0.025,0.108)); head.add(mk(S,dark,0.008,0.008,0.006,sd*0.04,0.025,0.114)); // eyes
      head.add(mk(U.box,dark,0.036,0.007,0.01,sd*0.04,0.05,0.106)); // brows
    }
    head.add(mk(U.box,M(0x7a3b30),0.04,0.008,0.01,0,-0.068,0.108)); // mouth
  }
  if(o.stache) head.add(mk(U.box,hair,0.07,0.014,0.02,0,-0.05,0.112));
  if(o.beard) head.add(mk(S,hair,0.078,0.04,0.075,0,-0.095,0.05));
  const ht=o.hairType||0;
  if(ht===3) head.add(mk(U.cap,M(o.skinDark||0x5a3a22),0.112,0.095,0.121,0,0.032,-0.004));
  else{
    head.add(mk(U.cap,hair,0.118,0.1,0.126,0,0.035,-0.005));
    if(ht===0) head.add(mk(U.box,hair,0.17,0.03,0.04,0,0.075,0.1));
    if(ht===1) for(let i=0;i<7;i++){ const a=i*0.9; head.add(mk(S,hair,0.045,0.045,0.045,Math.cos(a)*0.085,0.1+(i%3)*0.012,Math.sin(a)*0.09-0.01)); }
    if(ht===2) head.add(mk(U.box,hair,0.13,0.01,0.085,0,0.06,0.13));
    if(ht===4) head.add(mk(cylG(0.1,0.075,0.2,8),hair,1,1,0.7,0,-0.07,-0.09));
  }
  // --- legs (thigh, shorts, knee joint, calf, high socks, sneaker)
  const sl=Math.min(o.sl||0.4,0.5),hs=!!o.hsock;
  function leg(side){
    const g=new THREE.Group(); g.position.set(side*0.095*bw,0,0); hips.add(g);
    g.add(mk(cylG(0.095,0.066,0.43,sg),skin,1,1,1,0,-0.215,0,cast));
    const ts=Math.min(sl,0.43),rb=lerp(0.095,0.066,ts/0.43)+0.014;
    g.add(mk(cylG(0.106,rb,ts,sg),shorts,1,1,1,0,-ts/2,0,cast));
    const sh=new THREE.Group(); sh.position.set(0,-0.43,0); g.add(sh);
    sh.add(mk(cylG(0.06,0.042,0.42,sg),hs?sockM:skin,1,1,1,0,-0.21,0,cast));
    if(!lite){ sh.add(mk(S,skin,0.064,0.064,0.064,0,0,0.005,cast)); sh.add(mk(S,hs?sockM:skin,0.064,0.125,0.07,0,-0.12,-0.016,cast)); if(!hs) sh.add(mk(cylG(0.046,0.05,0.14,sg),sockM,1,1,1,0,-0.36,0,cast)); }
    if(sl>0.43) sh.add(mk(cylG(0.08,0.079,sl-0.43,sg),shorts,1,1,1,0,-(sl-0.43)/2,0,cast));
    sh.add(mk(U.box,shoe,0.105,0.07,0.26,0,-0.45,0.055,cast));
    if(!lite){ sh.add(mk(S,shoe,0.055,0.04,0.075,0,-0.44,0.18,cast)); sh.add(mk(S,shoe,0.05,0.045,0.05,0,-0.45,-0.075,cast)); sh.add(mk(U.box,sole,0.108,0.018,0.29,0,-0.488,0.06,cast)); }
    g.sh=sh; return g;
  }
  // --- arms (shoulder, sleeve, biceps, elbow, forearm, hand)
  function arm(side){
    const g=new THREE.Group(); g.position.set(side*0.238*bw,0.455,0); chest.add(g);
    const long=!!o.long,s1=long?0.29:0.2;
    g.add(mk(cylG(0.054,0.043,0.29,sg-2),skin,1,1,1,0,-0.145,0,cast));
    if(!lite) g.add(mk(S,long?shirt:skin,0.052,0.09,0.054,0,-0.1,0.008,cast));
    g.add(mk(cylG(0.063,0.054,s1,sg-2),shirt,1,1,1,0,-s1/2,0,cast));
    const fa=new THREE.Group(); fa.position.set(0,-0.29,0); g.add(fa);
    fa.add(mk(cylG(0.046,0.032,0.26,sg-2),long?shirt:skin,1,1,1,0,-0.13,0,cast));
    if(!lite) fa.add(mk(S,long?shirt:skin,0.048,0.085,0.05,0,-0.07,0.006,cast));
    fa.add(mk(S,skin,0.036,0.05,0.026,0,-0.29,0,cast));
    if(!lite) fa.add(mk(S,skin,0.014,0.03,0.014,-side*0.03,-0.27,0.018,cast));
    g.fa=fa; return g;
  }
  const c={root,body,hips,chest,head,legL:leg(-1),legR:leg(1),armL:arm(-1),armR:arm(1)};
  root.scale.setScalar((o.h||0.93)/0.93); return c;
}
function charAnim(c,st,dt,sp){
  if(c.real){ realAnim(c,st,dt,sp); return; }
  const run=Math.min(1,sp/5.2),amp=Math.min(1,sp/4.5)*0.9,ph=st.phase,s=Math.sin(ph),cp=Math.cos(ph);
  let lL=s*amp,lR=-s*amp;
  let kL=amp*(0.15+0.95*Math.max(0,-cp)),kR=amp*(0.15+0.95*Math.max(0,cp));
  let aL=-s*amp*0.95,aR=s*amp*0.95,elb=0.3+amp*0.95,az=0.07;
  let hipY=-s*0.24*amp,chY=s*0.3*amp,hipZ=s*0.05*amp;
  let lean=amp*0.1+run*0.12+clamp((st.acc||0)*0.014,-0.22,0.28),roll=clamp(-(st.turn||0)*0.045,-0.3,0.3)*(0.35+run);
  let by=(1-Math.cos(ph*2))*0.5*amp*0.07,crouch=0,tilt=0,yaw=0,headP=st.lookP||0,headY=st.look||0;
  // idle: breathing + weight shift
  if(amp<0.2){ hipZ=Math.sin(ph*0.18)*0.035; chY=Math.sin(ph*0.12)*0.05; c.chest.scale.y=1+Math.sin(ph*0.5)*0.012; } else c.chest.scale.y=1;
  // carrying the ball: slight crouch, head down, arms out for balance
  if(st.carry){ crouch=0.04; headP+=0.28; az=0.22; lean+=0.05; }
  // kick: wind-up -> strike -> follow-through, counter-rotation of hips/chest, plant-leg knee bend
  if(st.kickT>0){
    st.kickT+=dt/0.34; const k=st.kickT;
    if(k>=1) st.kickT=0; else{
      const a=k<0.35?lerp(0,0.95,k/0.35):k<0.6?lerp(0.95,-1.45,(k-0.35)/0.25):lerp(-1.45,0,(k-0.6)/0.4);
      lR=a; kR=k<0.35?0.9*(k/0.35):k<0.6?0.2:0.3; lL=0.12; kL=0.45;
      const e=k<0.35?-k/0.35*0.12:k<0.6?lerp(-0.12,0.25,(k-0.35)/0.25):lerp(0.25,0,(k-0.6)/0.4);
      lean=e+0.05; hipY=k<0.35?0.3*k/0.35:lerp(0.3,-0.35,clamp((k-0.35)/0.3,0,1))*(k<0.6?1:1-(k-0.6)/0.4); chY=-hipY*1.1;
      aL=-1.1*Math.sin(k*3.1); aR=0.9*Math.sin(k*3.1); az=0.55; crouch=0.07; headP=0.25;
    }
  }
  if(st.stun>0){ lean=0.38; aL=aR=-0.5; az=0.9; elb=0.5; headP=0.35; crouch=0.06; }
  if(st.pose==='ready'){ crouch=0.15; lL=0.4; lR=-0.35; kL=kR=0.85; aL=aR=-0.7; az=0.75; elb=0.7; lean=0.28; headP=-0.05; chY=0; hipY=0; }
  if(st.celebrate){
    const v=st.var||0; by=Math.abs(Math.sin(ph*0.6))*0.34; lL=lR=0.1; kL=kR=0.35*Math.abs(Math.sin(ph*0.6)); lean=-0.16; headP=-0.25; yaw=Math.sin(ph*0.4)*0.5; hipY=chY=0;
    if(v===0){ aL=aR=-3.05; az=0.5; elb=0.3; }
    else if(v===1){ aL=aR=0; az=1.45; elb=0.1; }
    else{ aL=-3.0; aR=-0.4; az=0.4; elb=0.9; }
  }
  if(st.diveT>0){
    const local=st.diveDir*Math.cos(st.heading); tilt=-Math.sign(local||1)*1.2*Math.min(1,(0.55-st.diveT)*6+0.3);
    aL=aR=-2.9; elb=0.1; lL=0.5; lR=-0.4; kL=0.3; kR=0.7; by=0.1; lean=0.05; hipY=chY=0;
  }
  if(st.pose==='gasp'){ aL=aR=-1.1; az=0.3; elb=0.8; headP=-0.1; }
  if(st.pose==='groan'){ aL=aR=-2.6; az=-0.25; elb=1.4; lean=0.15; headP=0.3; }
  c.legL.rotation.x=lL; c.legR.rotation.x=lR; c.legL.sh.rotation.x=kL; c.legR.sh.rotation.x=kR;
  c.armL.rotation.x=aL; c.armR.rotation.x=aR; c.armL.rotation.z=az; c.armR.rotation.z=-az; c.armL.fa.rotation.x=-elb; c.armR.fa.rotation.x=-elb;
  c.hips.rotation.y=hipY; c.hips.rotation.z=hipZ; c.chest.rotation.x=lean; c.chest.rotation.y=chY; c.chest.rotation.z=roll*0.6;
  c.head.rotation.y=headY-chY*0.6; c.head.rotation.x=headP-lean*0.5;
  c.body.position.y=by-crouch; c.body.rotation.z=tilt+roll*0.4; c.body.rotation.y=yaw;
}


/* =====================================================================
   REAL CHARACTER ASSETS (optional): put assets/manifest.json + FBX/GLB files.
   If anything is missing/fails, the game silently uses the procedural characters.
   ===================================================================== */
const REAL={ok:false,models:{},clips:{},cfg:null};
const OPT_LIBS=['https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/libs/fflate.min.js',
  'https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/loaders/FBXLoader.js',
  'https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/loaders/GLTFLoader.js',
  'https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/utils/SkeletonUtils.js'];
function matchClip(n){
  n=String(n||'');
  if(/idle|stand/i.test(n)) return 'idle'; if(/walk/i.test(n)) return 'walk'; if(/run|sprint|jog/i.test(n)) return 'run';
  if(/kick|shoot|strike|pass/i.test(n)) return 'kick'; if(/celebr|victory|cheer|dance/i.test(n)) return 'celebrate';
  if(/dive|save|catch/i.test(n)) return 'dive'; return null;
}
function loadAny(url){
  return new Promise((res,rej)=>{
    const ext=url.split('?')[0].split('.').pop().toLowerCase();
    if(ext==='fbx'){ if(!THREE.FBXLoader) return rej(new Error('FBXLoader missing')); new THREE.FBXLoader().load(url,o=>res({obj:o,clips:o.animations||[]}),undefined,rej); }
    else{ if(!THREE.GLTFLoader) return rej(new Error('GLTFLoader missing')); new THREE.GLTFLoader().load(url,g=>res({obj:g.scene,clips:g.animations||[]}),undefined,rej); }
  });
}
function prepModel(obj,cfg){
  obj.scale.setScalar(cfg.scale||1);
  obj.traverse(o=>{
    if(o.isMesh||o.isSkinnedMesh){ o.castShadow=true; o.receiveShadow=true; o.frustumCulled=false;
      const ms=Array.isArray(o.material)?o.material:[o.material];
      ms.forEach(m=>{ if(m&&m.map){ m.map.encoding=THREE.LinearEncoding; m.map.needsUpdate=true; } });
    }
  });
}
async function loadRealAssets(){
  if(location.protocol==='file:') return;
  let cfg; try{ const r=await fetch('assets/manifest.json',{cache:'no-cache'}); if(!r.ok) return; cfg=await r.json(); }catch(e){ return; }
  setProg(0.8,'تحميل الشخصيات…');
  for(const u of OPT_LIBS){ try{ await loadScript(u,9000); }catch(e){} }
  try{
    const models={},clips={},names=Object.keys(cfg.models||{});
    for(const k of names){ const r=await loadAny('assets/'+cfg.models[k]); prepModel(r.obj,cfg); models[k]=r; }
    for(const k of Object.keys(cfg.anims||{})){ const r=await loadAny('assets/'+cfg.anims[k]); const cl=r.clips&&r.clips[0]; if(cl){ cl.name=k; clips[k]=cl; } }
    for(const k of names) for(const cl of models[k].clips){ const n=matchClip(cl.name); if(n&&!clips[n]) clips[n]=cl; }
    if(!names.length) return;
    REAL.ok=true; REAL.models=models; REAL.clips=clips; REAL.cfg=cfg;
  }catch(e){ console.warn('Real assets failed, using procedural characters:',e); REAL.ok=false; }
}
function createRealChar(team,role){
  const key=(team?'B':'A')+'_'+(role==='GK'?'GK':'F');
  const R=REAL.models[key]||REAL.models[role==='GK'?'GK':'F']||REAL.models[Object.keys(REAL.models)[0]];
  const clone=THREE.SkeletonUtils?THREE.SkeletonUtils.clone(R.obj):R.obj.clone(true);
  const root=new THREE.Group(),holder=new THREE.Group(); holder.rotation.y=REAL.cfg.yaw||0; holder.add(clone); root.add(holder);
  const mixer=new THREE.AnimationMixer(clone),acts={};
  for(const k in REAL.clips){ const a=mixer.clipAction(REAL.clips[k]); if(k==='kick'||k==='dive'){ a.setLoop(THREE.LoopOnce,1); a.clampWhenFinished=true; } acts[k]=a; }
  return {root,body:holder,real:true,mixer,acts,cur:''};
}
function realAnim(c,st,dt,sp){
  let want='idle';
  if(st.celebrate) want='celebrate'; else if(st.diveT>0&&c.acts.dive) want='dive'; else if(st.kickT>0&&c.acts.kick) want='kick'; else if(sp>0.6) want=(sp<2.4&&c.acts.walk)?'walk':'run';
  if(st.kickT>0){ st.kickT+=dt/0.5; if(st.kickT>=1) st.kickT=0; }
  if(!c.acts[want]) want=c.acts.idle?'idle':Object.keys(c.acts)[0];
  if(want&&c.cur!==want){ c.acts[want].reset().fadeIn(want==='kick'?0.08:0.18).play(); if(c.cur&&c.acts[c.cur]) c.acts[c.cur].fadeOut(0.18); c.cur=want; }
  if(c.cur==='run'&&c.acts.run) c.acts.run.timeScale=clamp(sp/5.0,0.6,1.5);
  c.mixer.update(dt);
}

/* =====================================================================
   BUILD EVERYTHING
   ===================================================================== */
function buildLights(){
  scene.add(new THREE.HemisphereLight(0xffd6a8,0x5e4636,0.72));
  dirLight=new THREE.DirectionalLight(0xffc690,0.75); dirLight.position.set(-18,17,10); dirLight.castShadow=true;
  const sc=dirLight.shadow.camera; sc.left=-16;sc.right=16;sc.top=20;sc.bottom=-20;sc.near=5;sc.far=70;
  const ms=isTouch?1024:2048; dirLight.shadow.mapSize.set(ms,ms); dirLight.shadow.bias=-0.0006; scene.add(dirLight);
  for(const k of [[9.1,14.4],[-9.1,-14.4]]){ const sp=new THREE.SpotLight(0xfff0d0,0.65,48,0.95,0.6); sp.position.set(k[0],9.2,k[1]); sp.target.position.set(0,0,0); scene.add(sp); scene.add(sp.target); }
}
function buildGround(){
  const g=new THREE.Mesh(new THREE.PlaneGeometry(150,170),new THREE.MeshLambertMaterial({map:makeAsphaltTex()})); g.rotation.x=-Math.PI/2; g.receiveShadow=true; scene.add(g);
  const pm=new THREE.Mesh(new THREE.PlaneGeometry(20,30),new THREE.MeshLambertMaterial({map:makePitchTex(),transparent:true})); pm.rotation.x=-Math.PI/2; pm.position.y=0.03; pm.receiveShadow=true; scene.add(pm);
}

function chainTex(){
  const c=cv(64,64),g=c.getContext('2d'); g.strokeStyle='#fff'; g.lineWidth=3.4; g.lineCap='round';
  g.beginPath(); g.moveTo(32,0); g.lineTo(64,32); g.lineTo(32,64); g.lineTo(0,32); g.closePath(); g.stroke();
  const t=new THREE.CanvasTexture(c); t.wrapS=t.wrapT=THREE.RepeatWrapping; t.anisotropy=4; return t;
}
function buildCage(){
  const fx=PW+0.45,fz=PL+0.25,gapW=GW+0.25;
  const mat=new THREE.MeshBasicMaterial({map:chainTex(),transparent:true,alphaTest:0.3,side:THREE.DoubleSide,color:0xff8a2a});
  function panel(w,h,x,y,z,ry){ const g=new THREE.PlaneGeometry(w,h); scaleUV(g,w/0.55,h/0.55); const m=new THREE.Mesh(g,mat); m.position.set(x,y,z); m.rotation.y=ry; scene.add(m); }
  const kb=M(0x2f3644),post=new Inst(U.cyl,M(0xd9661a),false),rail=new Inst(U.box,M(0xd9661a),false);
  for(const sx of [-1,1]){
    panel(2*fz,2.7,sx*fx,2.25,0,Math.PI/2);
    scene.add(mk(U.box,kb,0.14,0.9,2*fz,sx*fx,0.45,0,true,true));
    rail.add(sx*fx,3.6,0,0,0.06,0.06,2*fz);
    for(let z=-fz;z<=fz+0.01;z+=fz/5) post.add(sx*fx,1.8,z,0,0.05,3.6,0.05);
  }
  for(const sz of [-1,1]){
    const segW=fx-gapW,cxs=(fx+gapW)/2;
    for(const sx of [-1,1]){
      panel(segW,2.7,sx*cxs,2.25,sz*fz,0);
      scene.add(mk(U.box,kb,segW,0.9,0.14,sx*cxs,0.45,sz*fz,true,true));
      rail.add(sx*cxs,3.6,sz*fz,0,segW,0.06,0.06);
      for(let x=gapW;x<=fx+0.01;x+=segW/2) post.add(sx*x,1.8,sz*fz,0,0.05,3.6,0.05);
    }
    panel(2*gapW,1.2,0,3.0,sz*fz,0); rail.add(0,3.6,sz*fz,0,2*gapW,0.06,0.06);
  }
  post.build(scene); rail.build(scene);
}
function buildFloodlights(){
  const gc=cv(128,128),g=gc.getContext('2d'),gr=g.createRadialGradient(64,64,0,64,64,64);
  gr.addColorStop(0,'rgba(255,248,220,1)'); gr.addColorStop(0.25,'rgba(255,230,170,.55)'); gr.addColorStop(1,'rgba(255,210,140,0)');
  g.fillStyle=gr; g.fillRect(0,0,128,128); const glow=new THREE.CanvasTexture(gc);
  for(const sx of [-1,1])for(const sz of [-1,1]){
    const x=sx*9.1,z=sz*14.4;
    scene.add(mk(U.cyl,M(0x2a2a2a),0.12,9,0.12,x,4.5,z,true));
    const head=new THREE.Group(); head.position.set(x,9.2,z); head.rotation.y=Math.atan2(-x,-z); scene.add(head);
    head.add(mk(U.box,M(0x1e1e1e),1.6,0.5,0.3,0,0,0));
    head.add(mk(U.box,new THREE.MeshBasicMaterial({color:0xfff6dc}),1.4,0.34,0.05,0,0,0.17));
    const sp=new THREE.Sprite(new THREE.SpriteMaterial({map:glow,blending:THREE.AdditiveBlending,depthWrite:false,transparent:true,opacity:0.9}));
    sp.scale.set(7,7,1); sp.position.set(x-sx*0.4,9.2,z-sz*0.4); scene.add(sp);
  }
}
function buildGraffiti(){
  const c=cv(1024,256),g=c.getContext('2d');
  g.fillStyle='#5d544b'; g.fillRect(0,0,1024,256);
  for(let i=0;i<900;i++){ g.fillStyle='rgba('+(rnd()<0.5?'30,26,22':'200,190,170')+','+(rnd()*0.08)+')'; g.fillRect(rnd()*1024,rnd()*256,2+rnd()*40,2+rnd()*10); }
  const cols=['#ff4d6d','#ffd23f','#2ec4b6','#4361ee','#ff8a1f','#8ac926'];
  for(let i=0;i<22;i++){ g.fillStyle=cols[i%6]; g.globalAlpha=0.55; g.beginPath(); g.ellipse(rnd()*1024,40+rnd()*180,30+rnd()*90,16+rnd()*40,rnd()*3,0,6.3); g.fill(); }
  g.globalAlpha=1; try{g.direction='rtl';}catch(e){}
  g.textAlign='center'; g.textBaseline='middle'; g.lineJoin='round';
  const tag=(t,x,y,sz,fill,stroke,rot)=>{ g.save(); g.translate(x,y); g.rotate(rot); g.font='900 '+sz+'px '+FONT; g.lineWidth=sz/7; g.strokeStyle=stroke; g.strokeText(t,0,0); g.fillStyle=fill; g.fillText(t,0,0); g.restore(); };
  tag('ملوك الشارع',500,120,118,'#ffd23f','#1b1b1b',-0.04);
  tag('حارتنا',170,60,62,'#2ec4b6','#12303a',0.1);
  tag('كابتن',860,70,58,'#ff7aa8','#4a1030',-0.12);
  tag('القاهرة',860,200,56,'#fff','#2b3a67',0.05);
  tag('★',90,200,64,'#ffd23f','#1b1b1b',0.2);
  g.strokeStyle='rgba(255,210,63,.7)'; g.lineWidth=5; for(let i=0;i<9;i++){ const x=90+rnd()*850; g.beginPath(); g.moveTo(x,170); g.lineTo(x+rnd()*4-2,170+30+rnd()*50); g.stroke(); }
  const t=tex(c);
  const wall=new THREE.Mesh(new THREE.PlaneGeometry(19,3.4),new THREE.MeshLambertMaterial({map:t})); wall.position.set(0,1.7,-18.3); scene.add(wall);
  scene.add(mk(U.box,M(0x4b443d),19.2,0.18,0.5,0,3.45,-18.3,false,true));
  scene.add(mk(U.box,M(0x4b443d),19,3.4,0.3,0,1.7,-18.45,true,true));
}
function buildFX(){
  // dust particles (single Points draw call, per-particle alpha/size)
  const N=56, geo=new THREE.BufferGeometry();
  const pos=new Float32Array(N*3),al=new Float32Array(N),sz=new Float32Array(N);
  geo.setAttribute('position',new THREE.BufferAttribute(pos,3)); geo.setAttribute('alpha',new THREE.BufferAttribute(al,1)); geo.setAttribute('size',new THREE.BufferAttribute(sz,1));
  const mat=new THREE.ShaderMaterial({transparent:true,depthWrite:false,
    vertexShader:'attribute float alpha;attribute float size;varying float vA;void main(){vA=alpha;vec4 mv=modelViewMatrix*vec4(position,1.0);gl_PointSize=size*(320.0/-mv.z);gl_Position=projectionMatrix*mv;}',
    fragmentShader:'varying float vA;void main(){float d=length(gl_PointCoord-vec2(0.5));float a=smoothstep(0.5,0.1,d)*vA;gl_FragColor=vec4(0.84,0.72,0.54,a);}'});
  const pts=new THREE.Points(geo,mat); pts.frustumCulled=false; scene.add(pts);
  dust={N,pos,al,sz,geo,pts,life:new Float32Array(N),max:new Float32Array(N),vx:new Float32Array(N),vy:new Float32Array(N),vz:new Float32Array(N),i:0,
    spawn(x,y,z,n,sp){ for(let k=0;k<n;k++){ const i=this.i; this.i=(this.i+1)%this.N; this.pos[i*3]=x+gauss()*0.12;this.pos[i*3+1]=y;this.pos[i*3+2]=z+gauss()*0.12; this.vx[i]=gauss()*sp;this.vy[i]=rr(0.3,1.1)*sp*0.5;this.vz[i]=gauss()*sp; this.max[i]=this.life[i]=rr(0.5,1.0); } },
    update(dt){ for(let i=0;i<this.N;i++){ if(this.life[i]>0){ this.life[i]-=dt; const k=Math.max(0,this.life[i]/this.max[i]); this.pos[i*3]+=this.vx[i]*dt;this.pos[i*3+1]+=this.vy[i]*dt;this.pos[i*3+2]+=this.vz[i]*dt; this.vx[i]*=0.95;this.vz[i]*=0.95;this.vy[i]*=0.94; this.al[i]=k*0.5; this.sz[i]=0.35+(1-k)*0.8; } else this.al[i]=0; }
      this.geo.attributes.position.needsUpdate=true; this.geo.attributes.alpha.needsUpdate=true; this.geo.attributes.size.needsUpdate=true; } };
  // footprints (instanced ring buffer)
  const fg=new THREE.PlaneGeometry(0.17,0.3); fg.rotateX(-Math.PI/2);
  fpMesh=new THREE.InstancedMesh(fg,new THREE.MeshBasicMaterial({color:0x5a4228,transparent:true,opacity:0.32,depthWrite:false,polygonOffset:true,polygonOffsetFactor:-2,polygonOffsetUnits:-2}),90);
  fpDummy=new THREE.Object3D(); fpDummy.position.y=-5; fpDummy.updateMatrix(); for(let i=0;i<90;i++) fpMesh.setMatrixAt(i,fpDummy.matrix);
  fpMesh.frustumCulled=false; scene.add(fpMesh);
}
function addFoot(x,z,h,side){
  fpDummy.position.set(x+Math.cos(h)*0.12*side,0.045,z-Math.sin(h)*0.12*side); fpDummy.rotation.set(0,h,0); fpDummy.updateMatrix();
  fpMesh.setMatrixAt(fpIdx,fpDummy.matrix); fpIdx=(fpIdx+1)%90; fpMesh.instanceMatrix.needsUpdate=true;
}
function buildBall(){
  const c=cv(128,128),g=c.getContext('2d'); g.fillStyle='#f4f1ea'; g.fillRect(0,0,128,128); g.fillStyle='#262626';
  for(let i=0;i<9;i++){ const x=(i%3)*46+14,y=((i/3)|0)*46+14; g.beginPath(); for(let k=0;k<5;k++){const a=k*1.2566-1.57;g.lineTo(x+Math.cos(a)*13,y+Math.sin(a)*13);} g.fill(); }
  ballMesh=new THREE.Mesh(new THREE.SphereGeometry(BR,12,10),new THREE.MeshLambertMaterial({map:tex(c)})); ballMesh.castShadow=true; scene.add(ballMesh);
  ball={x:0,y:BR,z:0,vx:0,vz:0,vy:0,owner:null,isShot:false};
  ringMesh=new THREE.Mesh(new THREE.RingGeometry(0.55,0.72,24),new THREE.MeshBasicMaterial({color:0xffe14d,side:THREE.DoubleSide,transparent:true,opacity:0.9,depthWrite:false})); ringMesh.rotation.x=-Math.PI/2; ringMesh.position.y=0.06; scene.add(ringMesh);
  arrowMesh=new THREE.Mesh(new THREE.ConeGeometry(0.17,0.34,4),new THREE.MeshBasicMaterial({color:0xffe14d})); arrowMesh.rotation.x=Math.PI; scene.add(arrowMesh);
  const ag=new THREE.PlaneGeometry(0.28,1); ag.translate(0,0.5,0); ag.rotateX(Math.PI/2);
  aimGroup=new THREE.Mesh(ag,new THREE.MeshBasicMaterial({color:0xffe14d,transparent:true,opacity:0.8,side:THREE.DoubleSide,depthWrite:false})); aimGroup.position.y=0.07; aimGroup.visible=false; scene.add(aimGroup);
}
const LOOKS=[
  [{skin:SKIN[2],skinDark:0x6a4630,shirt:'#2a9df4',shorts:0x3b5b8c,shoe:0xf4f4f4,hsock:true,sock:0xf4f4f4,hair:0x1a1410,hairType:0,sl:0.52,bw:1.0,h:0.94},
   {skin:SKIN[0],skinDark:0x7a5a3c,shirt:'#ffffff',shirt2:'#2a9df4',style:'stripeV',shorts:0x181818,shoe:0xe5533d,hair:0x2a1a10,hairType:1,stache:true,sl:0.42,bw:1.08,h:0.92},
   {skin:SKIN[3],skinDark:0x4a2e1c,shirt:'#9be22f',long:true,shorts:0x222222,shoe:0x222222,hair:0x120c08,hairType:2,beard:true,sl:0.5,bw:1.05,h:0.95}],
  [{skin:SKIN[4],skinDark:0x3a2414,shirt:'#ff7a1a',shorts:0x6b6b70,shoe:0xffd23f,hsock:true,sock:0x222222,hair:0x120c08,hairType:0,sl:0.42,bw:0.95,h:0.96},
   {skin:SKIN[1],skinDark:0x7a5a3c,shirt:'#d62839',shirt2:'#1d1d1d',style:'stripeH',shorts:0x4a6fa5,shoe:0xffffff,hair:0x3a2314,hairType:4,sl:0.55,bw:1.1,h:0.93},
   {skin:SKIN[5],skinDark:0x6a4630,shirt:'#8e44ad',long:true,shorts:0x222222,shoe:0x111111,hair:0x1a1410,hairType:3,stache:true,sl:0.5,bw:1.12,h:0.94}]
];
function buildPlayers(){
  ringMesh.visible=false;
  for(let T=0;T<2;T++) for(let i=0;i<3;i++){
    const ch=REAL.ok?createRealChar(T,i===0?'GK':'F'):createChar(LOOKS[T][i]); scene.add(ch.root);
    const p={team:T,slot:i-1,gk:i===0,ch,x:0,z:0,vx:0,vz:0,heading:T===0?Math.PI:0,phase:rnd()*6,kickT:0,celebrate:false,diveT:0,diveDir:1,
      noPick:0,tackleCD:0,stun:0,decT:0,supT:0,shootCD:1,holdT:0,react:0,aimErr:0,tx:0,tz:0,pose:'',stepSide:1,lastS:0,skill:DIFF.gkSkill,name:'p'+T+i,var:i};
    P.push(p); TM[T].push(p);
  }
}
function buildSpectators(){
  const spots=[[-9.0,-11.2],[-9.1,-10.3],[-9.0,0.5],[9.0,-6.8],[9.2,-5.9],[9.0,8.6],[-4.6,-16.2],[5.2,-16.6],[-3.2,16.0],[4.2,16.4]];
  const shirts=['#e9c46a','#2a9d8f','#e76f51','#8d99ae','#6a994e','#bc4749','#f4a261','#457b9d'];
  spots.forEach((s,i)=>{
    const ch=createChar({skin:SKIN[i%6],skinDark:0x5a3a22,shirt:shirts[i%8],shorts:i%2?0x3b4a6b:0x444444,shoe:i%3?0x222222:0xdddddd,hair:0x1a120c,hairType:(i*3)%5,stache:i%4===1,sl:i%2?0.5:0.42,bw:0.95+(i%3)*0.06,h:i===1||i===4||i===7?0.8:0.93,cast:false});
    ch.root.position.set(s[0],0,s[1]); const hd=Math.atan2(-s[0]*0.6,-s[1]); ch.root.rotation.y=hd;
    scene.add(ch.root); specs.push({ch,x:s[0],z:s[1],h:hd,ph:rnd()*6,st:{phase:rnd()*6,kickT:0,celebrate:false,diveT:0,diveDir:1,heading:hd,pose:''},react:0,type:''});
  });
  // background walkers on the far street (outside the pitch)
  for(let i=0;i<2;i++){
    const ch=createChar({skin:SKIN[(i+2)%6],skinDark:0x5a3a22,shirt:i?'#bcd':'#c97b4a',shorts:0x333333,shoe:0x222,hair:0x111,hairType:i,cast:false});
    scene.add(ch.root); walkers.push({ch,z:i?-21.5:-19.6,x:i?9:-8,dir:i?-1:1,sp:rr(1.0,1.5),st:{phase:rnd()*6,kickT:0,celebrate:false,diveT:0,diveDir:1,heading:0,pose:''}});
  }
}

/* =====================================================================
   GAME LOGIC
   ===================================================================== */
function startPos(p){
  const T=p.team,s=T===0?1:-1;
  if(p.gk) return [0,s*(PL-1.2)];
  const kicker=(T===kickTeam&&p.slot===0);
  if(kicker) return [0,s*0.9];
  if(p.slot===0) return [T===0?-2.8:2.8,s*3.4];
  return [T===0?3:-3,s*6.2];
}
function resetPositions(kt,snap){
  kickTeam=kt; ball.owner=null; ball.x=0;ball.z=0;ball.y=BR;ball.vx=ball.vz=ball.vy=0;ball.isShot=false; lastKick=null;
  for(const p of P){ const sp=startPos(p); p.tx=sp[0]; p.tz=sp[1]; if(snap){p.x=sp[0];p.z=sp[1];p.vx=p.vz=0;}
    p.celebrate=false;p.diveT=0;p.noPick=0;p.stun=0;p.tackleCD=0;p.decT=0;p.supT=0;p.shootCD=1;p.pose='';p.kickT=0;
    p.heading=p.team===0?Math.PI:0; }
  active=TM[0][1]; activeLock=0; input.charge=0;
}
function steer(p,dvx,dvz,dt,acc){
  const ax=dvx-p.vx,az=dvz-p.vz,m=Math.hypot(ax,az),mx=acc*dt;
  if(m>mx){p.vx+=ax/m*mx;p.vz+=az/m*mx;}else{p.vx=dvx;p.vz=dvz;}
}
function moveTo(p,tx,tz,spd,dt,arrive){
  const dx=tx-p.x,dz=tz-p.z,d=Math.hypot(dx,dz); let s=spd; if(arrive!==false) s=Math.min(spd,d*3.2); if(d<0.06) s=0;
  const k=d>0?s/d:0,f=p.stun>0?0.35:1; steer(p,dx*k*f,dz*k*f,dt,20);
}
function clampP(p){
  p.x=clamp(p.x,-PW+0.25,PW-0.25); p.z=clamp(p.z,-PL+0.25,PL-0.25);
  if(p.gk){ const oz=p.team===0?1:-1,a=oz*(PL-3.4),b=oz*(PL-0.45); p.x=clamp(p.x,-2.9,2.9); p.z=clamp(p.z,Math.min(a,b),Math.max(a,b)); }
}
function canKick(p){ return ball.owner===p||(!ball.owner&&Math.hypot(ball.x-p.x,ball.z-p.z)<1.05&&ball.y<0.8&&p.noPick<=0.15); }
function laneClear(a,b){
  let md=9; const vx=b.x-a.x,vz=b.z-a.z,l2=vx*vx+vz*vz||1;
  for(const o of TM[1-a.team]){ let t=clamp(((o.x-a.x)*vx+(o.z-a.z)*vz)/l2,0,1); const d=Math.hypot(a.x+vx*t-o.x,a.z+vz*t-o.z); if(d<md) md=d; }
  return md;
}
function pickPassTarget(p,hx,hz){
  let best=null,bs=-1e9; const atk=p.team===0?-1:1;
  for(const m of TM[p.team]){
    if(m===p) continue; const dx=m.x-p.x,dz=m.z-p.z,d=Math.hypot(dx,dz); if(d<1.8) continue;
    const open=laneClear(p,m); let s=Math.min(open,3.2)*1.5-d*0.1+(dz*atk)*0.12;
    if(m.gk) s-=5; if(open<0.75) s-=4;
    if(hx||hz){ const hn=Math.hypot(hx,hz)||1; s+=((dx*hx+dz*hz)/(d*hn))*2.2; }
    if(s>bs){bs=s;best={m,score:s,dist:d,open};}
  }
  return best;
}
function doKick(p,dx,dz,speed,vy,type){
  const n=Math.hypot(dx,dz)||1; dx/=n; dz/=n;
  ball.owner=null; ball.vx=dx*speed; ball.vz=dz*speed; ball.vy=vy; ball.isShot=(type==='shot');
  ball.x=p.x+dx*0.5; ball.z=p.z+dz*0.5;
  p.noPick=0.4; p.kickT=0.0001; p.heading=Math.atan2(dx,dz);
  lastKick={p,team:p.team,type,t:simTime,dist:0};
  audio.kick(speed/24);
  if(speed>14) dust.spawn(ball.x,0.12,ball.z,4,1.4);
  if(type==='shot'){
    const gk=TM[1-p.team][0]; gk.react=rr(DIFF.gkReact[0],DIFF.gkReact[1]); gk.aimErr=gauss()*DIFF.gkAimErr;
    const dg=Math.abs((p.team===0?-PL:PL)-p.z); if(dg<9) emit('bigshot',{p});
  }
}
function doPass(p,t){
  const m=t.m,d=t.dist,lead=clamp(d/14,0.1,0.8)*0.5;
  const dx=m.x+m.vx*lead-p.x,dz=m.z+m.vz*lead-p.z,dd=Math.hypot(dx,dz);
  doKick(p,dx,dz,clamp(dd*1.22+2.5,7,21),0.0,'pass'); lastKick.dist=d;
}
function doShot(p,charge,hx,hz,human){
  const atk=p.team===0?-1:1,gz=atk*PL,gk=TM[1-p.team][0]; let ax;
  if(human&&Math.abs(hx)>0.28) ax=clamp(hx,-1,1)*(GW-0.15);
  else ax=(gk.x>=0?-1:1)*rr(0.9,1.7);
  let ang=Math.atan2(ax-ball.x,gz-ball.z);
  ang+=(human?0.03+0.085*charge:DIFF.aiShotErr)*gauss();
  const sp=human?12+15*charge:rr(DIFF.aiShotSpeed[0],DIFF.aiShotSpeed[1]);
  const vy=human?0.8+3.2*charge*rnd():rr(0.5,3.0);
  doKick(p,Math.sin(ang),Math.cos(ang),sp,vy,'shot'); p.shootCD=1.4;
}
function switchPlayer(){ const o=TM[0].find(f=>!f.gk&&f!==active); if(o){active=o;activeLock=1.2;} }
function humanControl(p,dt){
  let jx=input.jx,jy=input.jy;
  if(kb.l||kb.r||kb.u||kb.d){ jx=(kb.r?1:0)-(kb.l?1:0); jy=(kb.d?1:0)-(kb.u?1:0); const m=Math.hypot(jx,jy); if(m>1){jx/=m;jy/=m;} }
  const sprint=input.sprint||kb.s, maxs=(sprint?6.1:4.9)*(ball.owner===p?0.95:1), f=p.stun>0?0.4:1;
  steer(p,jx*maxs*f,jy*maxs*f,dt,(jx||jy)?28:22);
  const has=canKick(p);
  if(input.passQ){ input.passQ=false;
    if(has){ const t=pickPassTarget(p,jx,jy); if(t&&t.score>-8) doPass(p,t); else doKick(p,jx||Math.sin(p.heading),jy||Math.cos(p.heading),11,0,'pass'); }
    else switchPlayer(); }
  if(input.shootRel){ const ch=input.charge; input.shootRel=false; input.charge=0; if(has) doShot(p,Math.max(0.12,ch),jx,jy,true); }
  else if(input.shootHeld&&has) input.charge=Math.min(1,input.charge+dt/0.9);
  else input.charge=0;
}
function chooseActive(dt){
  activeLock-=dt; const o=ball.owner;
  if(o&&o.team===0&&!o.gk){ active=o; return; }
  let best=null,bd=1e9;
  for(const f of TM[0]){ if(f.gk) continue; const d=Math.hypot(f.x-(ball.x+ball.vx*0.15),f.z-(ball.z+ball.vz*0.15)); if(d<bd){bd=d;best=f;} }
  if(!active||active.gk) active=best;
  else if(best!==active&&activeLock<=0&&bd<Math.hypot(active.x-ball.x,active.z-ball.z)-1.2){ active=best; activeLock=0.5; }
}
function nearestOpp(p){ let b=null,bd=1e9; for(const o of TM[1-p.team]){ const d=Math.hypot(o.x-p.x,o.z-p.z); if(d<bd){bd=d;b=o;} } return {o:b,d:bd}; }
function teamPlan(T){
  const o=ball.owner; let ch=null;
  if(!(o&&o.team===T)){
    const bx=ball.x+ball.vx*0.15,bz=ball.z+ball.vz*0.15; let bd=1e9;
    for(const f of TM[T]){ if(f.gk) continue; let d=Math.hypot(f.x-bx,f.z-bz); if(f===plan[T].chaser) d-=1.2; if(d<bd){bd=d;ch=f;} }
  }
  plan[T].chaser=ch;
}
function fieldAI(p,dt){
  const T=p.team,atk=T===0?-1:1,gz=atk*PL,ownZ=-gz,o=ball.owner,spd=DIFF.aiSpeed;
  p.supT-=dt; p.decT-=dt; p.shootCD-=dt;
  if(o===p){
    const dg=Math.abs(gz-p.z),near=nearestOpp(p);
    if(p.decT<=0){ p.decT=rr(0.18,0.34);
      if(dg<9.5&&p.shootCD<=0){ // shoot if lane to goal isn't blocked
        let blocked=false; for(const q of TM[1-T]){ if(q.gk) continue; const t=clamp(((q.x-p.x)*(0-p.x)+(q.z-p.z)*(gz-p.z))/(((0-p.x)**2+(gz-p.z)**2)||1),0,1); if(Math.hypot(p.x+(0-p.x)*t-q.x,p.z+(gz-p.z)*t-q.z)<0.8) blocked=true; }
        if(!blocked&&rnd()<(dg<6?0.7:0.4)){ doShot(p,0,0,0,false); return; }
      }
      if(near.d<1.9&&rnd()<0.5){ const t=pickPassTarget(p,0,0); if(t&&t.score>0){ doPass(p,t); return; } }
    }
    let tx=clamp(p.x*0.6,-2.5,2.5),tz=gz,dx=tx-p.x,dz=tz-p.z,dn=Math.hypot(dx,dz)||1; dx/=dn;dz/=dn;
    for(const q of TM[1-T]){ if(q.gk) continue; const rx=q.x-p.x,rz=q.z-p.z,d=Math.hypot(rx,rz);
      if(d<2.6&&(rx*dx+rz*dz)>0){ const side=(rx*dz-rz*dx)>0?-1:1; dx+=-dz*side*(1-d/2.6)*1.4; dz+=dx*side*(1-d/2.6)*0.0+dx*0; } }
    const m=Math.hypot(dx,dz)||1,f=p.stun>0?0.35:1; steer(p,dx/m*spd*0.93*f,dz/m*spd*0.93*f,dt,18);
    return;
  }
  if(o&&o.team===T){ // support: find open space ahead
    if(p.supT<=0){ p.supT=0.5;
      const cands=[[-4.6,3.5],[4.6,3.5],[-5.2,0.5],[5.2,0.5],[0,6],[-2.5,5],[2.5,5]]; let bs=-1e9,bx=p.x,bz=p.z;
      for(const c of cands){ const x=clamp(o.x*0.4+c[0],-PW+1,PW-1),z=clamp(o.z+atk*c[1],-PL+1.5,PL-1.5);
        const s=Math.min(laneClear(o,{x,z}),3)*1.5-Math.hypot(x-p.x,z-p.z)*0.12+(x*o.x<0?0.8:0); if(s>bs){bs=s;bx=x;bz=z;} }
      p.tx=bx;p.tz=bz; }
    moveTo(p,p.tx,p.tz,spd,dt); return;
  }
  if(plan[T].chaser===p){ // pursue ball / carrier
    if(o) moveTo(p,o.x+o.vx*0.2,o.z+o.vz*0.2,spd*1.02,dt,false); else moveTo(p,ball.x+ball.vx*0.2,ball.z+ball.vz*0.2,spd*1.05,dt,false);
    return;
  }
  if(o){ // mark: block the lane to the other attacker
    const other=TM[1-T].find(q=>!q.gk&&q!==o); const t=other||o;
    moveTo(p,lerp(o.x,t.x,0.55),lerp(o.z,t.z,0.55)+(ownZ-o.z)*0.05,spd,dt);
  }else{ moveTo(p,clamp(lerp(0,ball.x,0.5),-5.5,5.5),lerp(ownZ,ball.z,0.5),spd,dt); }
}
function gkDistribute(p){
  const t=pickPassTarget(p,0,0); const fw=p.team===0?-1:1;
  if(t&&t.score>-6) doPass(p,t); else doKick(p,rr(-0.3,0.3),fw,12,0,'pass');
}
function gkAI(p,dt){
  const T=p.team,ownZ=T===0?PL:-PL,inw=-Math.sign(ownZ),lineZ=ownZ+inw*1.2;
  if(ball.owner===p){ p.holdT-=dt; steer(p,0,0,dt,20); p.heading=Math.atan2(0,inw); if(p.holdT<=0) gkDistribute(p); return; }
  p.react-=dt; let tx=clamp(ball.x*0.4,-1.7,1.7),tz=lineZ;
  const toward=(ball.vz*Math.sign(ownZ))>2.5;
  if(toward&&ball.isShot){ const t=(lineZ-ball.z)/ball.vz; if(t>0&&t<1.3) tx=clamp(ball.x+ball.vx*t+p.aimErr,-GW-0.6,GW+0.6); }
  const bd=Math.hypot(ball.x-p.x,ball.z-p.z);
  if(!ball.owner&&Math.abs(ball.z-ownZ)<4.2&&Math.hypot(ball.vx,ball.vz)<5&&Math.abs(ball.x)<3.6){ tx=ball.x; tz=ball.z; }
  if(p.diveT<=0&&toward&&ball.isShot&&p.react<=0&&bd<4.6){ const dxp=tx-p.x; if(Math.abs(dxp)>0.9){ p.diveT=0.55; p.diveDir=Math.sign(dxp); } }
  if(p.diveT>0){ p.diveT-=dt; steer(p,p.diveDir*6.6,0,dt,60); }
  else if(p.react>0&&ball.isShot) steer(p,0,0,dt,20);
  else moveTo(p,tx,tz,5.2,dt);
  p.heading+=angDiff(p.heading,Math.atan2(ball.x-p.x,ball.z-p.z))*Math.min(1,dt*8);
}
function takePossession(p){
  const lk=lastKick;
  if(lk&&lk.p!==p&&simTime-lk.t<3.5&&lk.type==='pass'){
    if(lk.team===p.team){ if(lk.team===0&&lk.dist>5.5) emit('goodpass',{p:lk.p}); }
    else emit('intercept',{p});
  }
  ball.owner=p; ball.isShot=false; if(p.gk) p.holdT=rr(0.8,1.4);
}
function gkTouch(p){
  p.noPick=0.4; const sp=Math.hypot(ball.vx,ball.vz);
  if(ball.isShot){
    if(rnd()>p.skill){ p.noPick=0.6; return; } // flubbed it
    const shooter=lastKick?lastKick.team:1-p.team;
    if(sp<12&&rnd()<0.7){ takePossession(p); }
    else{ ball.vz=-ball.vz*0.45; ball.vx=ball.vx*0.3+rr(-3,3); ball.vy=rr(1.5,3.5); ball.isShot=false; audio.thud(); }
    emit('save',{shooter});
  }else takePossession(p);
}
function updatePickups(dt){
  if(ball.owner||state!=='play') return;
  for(const p of P){
    if(p.noPick>0) continue;
    const d=Math.hypot(p.x-ball.x,p.z-ball.z),reach=p.gk?(p.diveT>0?1.5:0.85):0.62;
    if(d<reach&&ball.y<(p.gk?2.0:0.75)){
      if(p.gk){ gkTouch(p); break; }
      const sp=Math.hypot(ball.vx,ball.vz),same=lastKick&&lastKick.team===p.team;
      if(ball.isShot&&!same){ ball.vx*=-0.3; ball.vz*=-0.3; ball.vy=2; ball.isShot=false; p.noPick=0.3; audio.thud(); }
      else if(sp<15||(same&&sp<24)){ takePossession(p); break; }
      else{ ball.vx*=0.4; ball.vz*=0.4; p.noPick=0.25; audio.thud(); }
    }
  }
}
function updateTackles(dt){
  const o=ball.owner; if(!o||o.gk||state!=='play') return;
  for(const t of TM[1-o.team]){
    if(t.gk||t.tackleCD>0||t.stun>0) continue;
    if(Math.hypot(t.x-o.x,t.z-o.z)<0.85){
      t.tackleCD=0.75; const sprinting=Math.hypot(o.vx,o.vz)>5; let ch=(o.team===0?DIFF.tackleVsHuman:DIFF.tackleVsAI)-(sprinting?0.1:0);
      if(rnd()<ch){ ball.owner=t; ball.isShot=false; o.stun=0.55; dust.spawn(o.x,0.1,o.z,5,1.6); emit('steal',{p:t,victim:o}); break; }
      else{ t.stun=0.4; if(o.team===0) emit('dribble',{p:o}); }
    }
  }
}
function updateBall(dt){
  const b=ball;
  if(b.owner){
    const o=b.owner,fx=Math.sin(o.heading),fz=Math.cos(o.heading),sp=Math.hypot(o.vx,o.vz),dist=0.52+Math.min(0.22,sp*0.04);
    const tx=o.x+fx*dist,tz=o.z+fz*dist,k=Math.min(1,dt*20);
    b.x+=(tx-b.x)*k; b.z+=(tz-b.z)*k; b.vx=o.vx; b.vz=o.vz; b.y=BR+Math.abs(Math.sin(o.phase))*0.05*Math.min(1,sp/3); b.vy=0; return;
  }
  const sub=2,h=dt/sub; let goalFor=-1;
  for(let i=0;i<sub;i++){
    b.vy-=GRAV*h; b.x+=b.vx*h; b.y+=b.vy*h; b.z+=b.vz*h;
    if(b.y<BR){ b.y=BR; if(b.vy<-1.5){ if(b.vy<-4) dust.spawn(b.x,0.12,b.z,2,1); b.vy=-b.vy*0.5; } else b.vy=0; const f=Math.exp(-1.15*h); b.vx*=f; b.vz*=f; if(Math.hypot(b.vx,b.vz)<0.04){b.vx=0;b.vz=0;} }
    else{ const f=Math.exp(-0.12*h); b.vx*=f; b.vz*=f; }
    if(state==='goal'){ // inside the net
      if(Math.abs(b.x)>GW-0.12){ b.x=Math.sign(b.x)*(GW-0.12); b.vx=-b.vx*0.3; }
      const lim=PL+1.4; if(Math.abs(b.z)>lim){ b.z=Math.sign(b.z)*lim; b.vz=-b.vz*0.25; }
      if(b.y>GH-0.1){ b.y=GH-0.1; b.vy=-Math.abs(b.vy)*0.2; }
      continue;
    }
    if(Math.abs(b.x)>PW+0.3){ b.x=Math.sign(b.x)*(PW+0.3); b.vx=-b.vx*0.6; if(b.isShot){b.isShot=false;emit('miss',{});} }
    // goal posts
    for(const sx of [-GW,GW])for(const sz of [-PL,PL]){
      const dx=b.x-sx,dz=b.z-sz,d=Math.hypot(dx,dz);
      if(d<BR+0.09&&d>0.001&&b.y<GH+0.1){ const nx=dx/d,nz=dz/d,vn=b.vx*nx+b.vz*nz; if(vn<0){ b.vx-=1.7*vn*nx; b.vz-=1.7*vn*nz; b.vx*=0.8;b.vz*=0.8; audio.post(); if(b.isShot){b.isShot=false;emit('post',{});} } b.x=sx+nx*(BR+0.1); b.z=sz+nz*(BR+0.1); }
    }
    if(Math.abs(b.z)>PL){
      const inMouth=Math.abs(b.x)<GW-0.05&&b.y<GH;
      if(inMouth&&Math.abs(b.z)>PL+0.15){ goalFor=b.z<0?0:1; break; }
      if(!inMouth){ b.z=Math.sign(b.z)*PL; b.vz=-b.vz*0.45; b.vx*=0.85; if(b.isShot){b.isShot=false;emit('miss',{});} }
    }
  }
  if(goalFor>=0) onGoal(goalFor);
}
function separate(){
  for(let i=0;i<P.length;i++)for(let j=i+1;j<P.length;j++){
    const a=P[i],b=P[j],dx=b.x-a.x,dz=b.z-a.z,d=Math.hypot(dx,dz);
    if(d<0.62&&d>0.001){ const ov=(0.62-d)/2,nx=dx/d,nz=dz/d; a.x-=nx*ov;a.z-=nz*ov;b.x+=nx*ov;b.z+=nz*ov; }
  }
}
function tickTimers(dt){ for(const p of P){ p.noPick-=dt;p.tackleCD-=dt;p.stun-=dt; if(p.kickT<0)p.kickT=0; } }
function integrate(p,dt){
  p.x+=p.vx*dt; p.z+=p.vz*dt; clampP(p);
  const sp=Math.hypot(p.vx,p.vz);
  if(sp>0.4&&!p.gk||sp>0.4&&p.diveT<=0) p.heading+=angDiff(p.heading,Math.atan2(p.vx,p.vz))*Math.min(1,dt*(p.team===0&&p===active?12:9));
}
function stepPlay(dt){
  clock-=dt; if(clock<=0){ clock=0; finishMatch(); return; }
  tickTimers(dt); chooseActive(dt); teamPlan(0); teamPlan(1);
  for(const p of P){
    if(p===active) humanControl(p,dt);
    else if(p.gk) gkAI(p,dt); else fieldAI(p,dt);
  }
  for(const p of P) integrate(p,dt);
  separate(); updateBall(dt); updatePickups(dt); updateTackles(dt);
  bubbleCD-=dt;
}
function stepReady(dt){
  stateT-=dt; tickTimers(dt);
  for(const p of P) moveTo(p,p.tx,p.tz,8,dt);
  for(const p of P) integrate(p,dt);
  ball.x=0;ball.z=0;ball.y=BR;ball.vx=ball.vz=0;
  if(stateT<=0){ for(const p of P){p.x=p.tx;p.z=p.tz;p.vx=p.vz=0;} const k=TM[kickTeam][1]; k.heading=kickTeam===0?Math.PI:0; ball.owner=k; state='play'; audio.whistle(false); }
}
function stepCountdown(dt){
  cdT-=dt; const n=cdT>2.6?'3':cdT>1.6?'2':cdT>0.6?'1':'يلا!';
  if($('cdText').dataset.v!==n){ $('cdText').dataset.v=n; $('cdText').textContent=n; $('cdText').classList.remove('pop'); void $('cdText').offsetWidth; $('cdText').classList.add('pop'); }
  for(const p of P){ steer(p,0,0,dt,20); }
  ball.x=0;ball.z=0;ball.y=BR;
  if(cdT<=0){ $('cdText').textContent=''; $('cdText').dataset.v=''; const k=TM[kickTeam][1]; ball.owner=k; state='play'; audio.whistle(false); }
}
function stepGoal(dt){
  stateT-=dt; tickTimers(dt); for(const p of P) steer(p,0,0,dt,10);
  updateBall(dt);
  if(stateT<=0){
    resetPositions(kickTeam,false); state='ready'; stateT=1.8; audio.whistle(false);
    for(const p of P){ const sp=startPos(p); p.tx=sp[0]; p.tz=sp[1]; }
    ball.x=0;ball.z=0;
  }
}
function stepOver(dt){
  stateT-=dt; for(const p of P) steer(p,0,0,dt,10); updateBall(dt);
  if(stateT<=0&&mode==='match'&&!$('results').dataset.shown){ showResults(); }
}
function step(dt){
  simTime+=dt;
  if(state==='countdown') stepCountdown(dt); else if(state==='ready') stepReady(dt); else if(state==='play') stepPlay(dt);
  else if(state==='goal') stepGoal(dt); else if(state==='over') stepOver(dt);
  if(pendingSay){ pendingSay.t-=dt; if(pendingSay.t<=0){ say(pendingSay.text,pendingSay.who,true); pendingSay=null; } }
  if(mode==='match') audio.tick(dt);
}
function onGoal(team){
  score[team]++; state='goal'; stateT=2.7; ball.owner=null; ball.isShot=false; kickTeam=1-team;
  for(const p of TM[team]){ p.celebrate=true; }
  for(const p of TM[1-team]){ p.pose=''; }
  const gt=$('goalText'); gt.textContent=team===0?'جـــوووون!':'جون عليك!'; gt.classList.toggle('bad',team===1); gt.classList.remove('show'); void gt.offsetWidth; gt.classList.add('show');
  audio.whistle(false); if(team===0) audio.cheer(); else audio.groan();
  for(const s of specs){ s.react=2.6; s.type=team===0?'cheer':'groan'; }
  updateHud(true);
  const scorer=lastKick&&lastKick.team===team?lastKick.p:TM[team][1];
  if(team===0){ addStyle(500,'جووون!'); say('جوووون يا جدعان!','crowd',true); pendingSay={t:3.9,text:'هات التانية بقى!',who:scorer}; }
  else { say('يا حكم!',TM[0][1],true); }
}
function finishMatch(){
  state='over'; stateT=2.3; ball.owner=null; audio.whistle(true);
  const w=score[0]>score[1]?0:score[1]>score[0]?1:-1;
  if(w>=0) for(const p of TM[w]) p.celebrate=true;
  if(w===0){ audio.cheer(); for(const s of specs){s.react=3;s.type='cheer';} } else if(w===1){ audio.groan(); }
  $('cdText').textContent='';
}
function showResults(){
  $('results').dataset.shown='1';
  const d=score[0]-score[1]; settings.played++; if(d>0) settings.wins++; if(d>settings.best) settings.best=d;
  store.set('played',settings.played); store.set('wins',settings.wins); store.set('best',settings.best);
  $('resScore').textContent=score[0]+' : '+score[1];
  $('resText').textContent=d>0?'مبروك يا كابتن! كسبنا الماتش 🏆':d<0?'خسرنا المرة دي.. هات التانية بقى!':'تعادل.. ماتش جامد!';
  if(style>bestStyle){ bestStyle=style; store.set('bstyle',bestStyle); }
  $('resStat').textContent='STYLE: '+style+' (أفضل '+bestStyle+') · مباريات: '+settings.played+' · انتصارات: '+settings.wins+' · أفضل فارق: '+settings.best;
  $('results').classList.remove('hidden'); detachInput(); $('hud').classList.add('hidden');
}

/* ---------- events → commentary ---------- */
const LINES={dribble:['يا لهوي على المهارة!','الله عليك يا نجم!'],pass:['العب يا كابتن!','الله عليك يا نجم!']};
function onScreen(v3){ tmpV.set(v3.x,1.6,v3.z).project(camera); return tmpV.z<1&&Math.abs(tmpV.x)<0.8&&tmpV.y>-0.7&&tmpV.y<0.8; }
function crowdTarget(){ const vis=specs.filter(s=>onScreen(s.ch.root.position)); return vis.length?vis[(rnd()*vis.length)|0].ch.root:null; }
function say(text,who,force){
  if(mode!=='match') return;
  if(!force&&(bubbleCD>0||(lineCD[text]||0)>simTime)) return;
  let target=null;
  if(who==='crowd') target=crowdTarget();
  else if(who&&who.ch) target=who.ch.root; else if(who) target=who;
  if(!target&&who==='crowd'){ target=null; }
  showBubble(text,target);
  bubbleCD=1.5; lineCD[text]=simTime+6;
}
function pick(a){return a[(rnd()*a.length)|0];}
function emit(type,d){
  if(mode!=='match') return;
  switch(type){
    case 'dribble': say(pick(LINES.dribble),'crowd'); addStyle(150,'مراوغة'); break;
    case 'goodpass': say(pick(LINES.pass),'crowd'); addStyle(100,'تمريرة طويلة'); break;
    case 'steal': if(d.victim.team===0) say('وسع يا عم!',d.p); else addStyle(50,'استخلاص'); break;
    case 'intercept': if(d.p.team===1&&rnd()<0.5) say('وسع يا عم!',d.p); break;
    case 'bigshot': audio.gasp(); for(const s of specs){ if(s.react<=0){s.react=1.0;s.type='gasp';} } break;
    case 'save': say(d.shooter===0?'يا ابني حطها في الجون!':'الله عليك يا نجم!','crowd'); break;
    case 'miss': case 'post': if(lastKick&&lastKick.team===0) say('يا ابني حطها في الجون!','crowd'); break;
  }
}
function updateStyle(){ $('styleChip').textContent='STYLE '+style; }
function addStyle(n,label){
  if(mode!=='match') return; style+=n; updateStyle();
  const el=$('stylePop'); el.textContent=label+'  +'+n; el.classList.remove('show'); void el.offsetWidth; el.classList.add('show');
}
/* ---------- speech bubbles (DOM, projected from 3D) ---------- */
const bub=[];
function showBubble(text,target){
  if(!bub.length) return;
  let b=bub.find(x=>x.t<=0)||bub.reduce((a,c)=>a.t<c.t?a:c);
  b.t=2.1; b.target=target; b.el.textContent=text; b.el.classList.remove('pop'); void b.el.offsetWidth; b.el.classList.add('pop'); b.el.style.display='block';
  placeBubble(b);
}
function placeBubble(b){
  const W=window.innerWidth,H=window.innerHeight; let x=W/2,y=H*0.2;
  if(b.target){ tmpV.set(b.target.position.x,2.35,b.target.position.z).project(camera);
    if(tmpV.z<1){ x=(tmpV.x*0.5+0.5)*W; y=(-tmpV.y*0.5+0.5)*H; } }
  x=clamp(x,90,W-90); y=clamp(y,110,H-20);
  b.el.style.transform='translate('+Math.round(x)+'px,'+Math.round(y)+'px) translate(-50%,-100%)';
}
function updateBubbles(dt){ for(const b of bub){ if(b.t>0){ b.t-=dt; if(b.t<=0){ b.el.style.display='none'; continue; } placeBubble(b); } } }

/* =====================================================================
   VISUAL SYNC + CAMERA
   ===================================================================== */
function syncVisuals(dt){
  for(const p of P){
    const sp=Math.hypot(p.vx,p.vz);
    p.phase+=dt*(p.celebrate?8:4+sp*1.9);
    const s=Math.sin(p.phase); if(sp>2&&((s>0)!==(p.lastS>0))){ addFoot(p.x,p.z,p.heading,p.stepSide); p.stepSide=-p.stepSide; if(sp>4.6) dust.spawn(p.x,0.08,p.z,1,0.9); } p.lastS=s;
    const fw=p.vx*Math.sin(p.heading)+p.vz*Math.cos(p.heading),k8=Math.min(1,dt*8);
    p.acc=lerp(p.acc||0,(fw-(p.pf||0))/Math.max(dt,0.001),k8); p.pf=fw;
    p.turn=lerp(p.turn||0,angDiff(p.ph||p.heading,p.heading)/Math.max(dt,0.001),k8); p.ph=p.heading;
    p.carry=ball.owner===p&&!p.gk; p.stun_=p.stun>0; 
    const tb=Math.atan2(ball.x-p.x,ball.z-p.z); p.look=p.carry?0:clamp(angDiff(p.heading,tb),-0.9,0.9); p.lookP=p.carry?0:0.04;
    if(p.gk&&state==='play'&&!ball.owner&&ball.isShot&&p.diveT<=0) p.pose='ready'; else if(p.pose==='ready') p.pose='';
    p.stun=p.stun; const stv=p.stun; p.stunFlag=stv>0;
    charAnim(p.ch,p,dt,sp);
    p.ch.root.position.set(p.x,0,p.z); p.ch.root.rotation.y=p.heading;
  }
  // ball
  ballMesh.position.set(ball.x,ball.y,ball.z);
  const bvx=ball.owner?ball.owner.vx:ball.vx,bvz=ball.owner?ball.owner.vz:ball.vz;
  ballMesh.rotation.x+=bvz*dt/BR; ballMesh.rotation.z-=bvx*dt/BR;
  // active marker + aim indicator
  const showMark=mode==='match'&&active&&(state==='play'||state==='ready'||state==='countdown');
  ringMesh.visible=arrowMesh.visible=!!showMark;
  if(showMark){ ringMesh.position.x=active.x; ringMesh.position.z=active.z; arrowMesh.position.set(active.x,2.35+Math.sin(simTime*6)*0.08,active.z); }
  const charging=showMark&&state==='play'&&input.charge>0.02&&canKick(active);
  aimGroup.visible=charging;
  if(charging){
    let hx=input.jx; if(kb.l||kb.r) hx=(kb.r?1:0)-(kb.l?1:0);
    const gz=-PL; let ax; if(Math.abs(hx)>0.28) ax=clamp(hx,-1,1)*(GW-0.15); else{ const gk=TM[1][0]; ax=(gk.x>=0?-1:1)*1.3; }
    const ang=Math.atan2(ax-active.x,gz-active.z); aimGroup.position.set(active.x,0.07,active.z); aimGroup.rotation.y=ang; aimGroup.scale.set(1,1.5+input.charge*5,1);
  }
  // spectators
  for(const s of specs){
    s.ph+=dt; if(s.react>0){ s.react-=dt; } const st=s.st;
    st.pose=s.react>0&&s.type!=='cheer'?s.type:''; st.celebrate=s.react>0&&s.type==='cheer'; st.phase+=dt*(st.celebrate?9:1.2);
    let tx=ball.x-s.x,tz=ball.z-s.z; const th=Math.atan2(tx,tz); s.h+=angDiff(s.h,lerp(Math.atan2(-s.x,-s.z),th,0.5))*Math.min(1,dt*2);
    st.heading=s.h; st.look=clamp(angDiff(s.h,Math.atan2(ball.x-s.x,ball.z-s.z)),-0.8,0.8); st.var=(s.ph|0)%3; charAnim(s.ch,st,dt,0); s.ch.root.rotation.y=s.h;
    if(!st.celebrate) s.ch.body.rotation.z=Math.sin(s.ph*1.1)*0.025;
  }
  for(const w of walkers){
    w.x+=w.dir*w.sp*dt; if(w.x>11){w.dir=-1;} if(w.x<-11){w.dir=1;}
    const st=w.st; st.phase+=dt*(4+w.sp*1.9); charAnim(w.ch,st,dt,w.sp*1.6); w.ch.root.position.set(w.x,0,w.z); w.ch.root.rotation.y=w.dir>0?Math.PI/2:-Math.PI/2;
  }
  for(const m of laundry){ m.rotation.y=m.userData.by+Math.sin(simTime*1.4+m.userData.ph)*0.18; }
  dust.update(dt);
}
function updateCamera(dt){
  let lx,lz,cx,cy,cz;
  const asp=window.innerWidth/Math.max(1,window.innerHeight);
  if(mode!=='match'){
    menuT+=dt; const a=Math.sin(menuT*0.18)*0.55;
    cx=Math.sin(a)*23; cy=10.5; cz=Math.cos(a)*23; lx=0; lz=-4;
    const k=1-Math.exp(-2*dt); if(!camS.init){camS.x=cx;camS.y=cy;camS.z=cz;camS.lx=lx;camS.lz=lz;camS.init=true;}
    camS.x+=(cx-camS.x)*k;camS.y+=(cy-camS.y)*k;camS.z+=(cz-camS.z)*k;camS.lx+=(lx-camS.lx)*k;camS.lz+=(lz-camS.lz)*k;
    camera.position.set(camS.x,camS.y,camS.z); camera.lookAt(camS.lx,1.2,camS.lz); return;
  }
  let fx,fz;
  if(state==='ready'||state==='countdown'){ fx=0;fz=0; }
  else if(state==='goal'||state==='over'){ fx=ball.x;fz=ball.z; }
  else{ const a=active||P[1]; const w=0.45; fx=lerp(a.x,ball.x,w); fz=lerp(a.z,ball.z,w); }
  const sc=asp<0.7?1.1:asp<1?1.04:1;
  lx=clamp(fx*0.8,-5.5,5.5); lz=clamp(fz-1.5,-10,9);
  cx=lx*0.9; cy=10.6*sc; cz=lz+12.6*sc;
  const k=1-Math.exp(-3.2*dt);
  if(!camS.init){camS.x=cx;camS.y=cy;camS.z=cz;camS.lx=lx;camS.lz=lz;camS.init=true;}
  camS.x+=(cx-camS.x)*k;camS.y+=(cy-camS.y)*k;camS.z+=(cz-camS.z)*k;camS.lx+=(lx-camS.lx)*k;camS.lz+=(lz-camS.lz)*k;
  camera.position.set(camS.x,camS.y,camS.z); camera.lookAt(camS.lx,0.6,camS.lz);
}
function resize(){
  const w=window.innerWidth,h=window.innerHeight; if(!renderer) return;
  renderer.setPixelRatio(quality.pr); renderer.setSize(w,h,false);
  const asp=w/Math.max(1,h); camera.aspect=asp; camera.fov=asp<0.8?70:asp<1.2?60:52; camera.updateProjectionMatrix();
}
function adapt(dt){
  fpsAcc+=dt; fpsN++; fpsTimer+=dt;
  if(fpsTimer>=3){ const avg=fpsAcc/fpsN; fpsAcc=0;fpsN=0;fpsTimer=0;
    if(avg>0.026&&quality.level<2){ quality.level++; if(quality.level===1){ quality.pr=1; resize(); } else { dirLight.castShadow=false; renderer.shadowMap.enabled=false; } } }
}

/* =====================================================================
   HUD / UI
   ===================================================================== */
function fmt(t){ t=Math.max(0,Math.ceil(t)); return Math.floor(t/60)+':'+String(t%60).padStart(2,'0'); }
function updateHud(force){
  const t=fmt(clock); if(force||hudCache.t!==t){ hudCache.t=t; $('clock').textContent=t; $('clock').classList.toggle('low',clock<=15); }
  if(force||hudCache.s0!==score[0]){hudCache.s0=score[0];$('s0').textContent=score[0];}
  if(force||hudCache.s1!==score[1]){hudCache.s1=score[1];$('s1').textContent=score[1];}
  const deg=Math.round(input.charge*360); if(hudCache.c!==deg){ hudCache.c=deg; $('bShoot').style.background='conic-gradient(#ffe14d '+deg+'deg, rgba(255,255,255,.18) 0)'; }
}
function showOnly(id){ for(const s of ['menu','tutorial','pause','results']) $(s).classList.toggle('hidden',s!==id); }
function applyDur(){ document.querySelectorAll('#durSeg button').forEach(b=>b.classList.toggle('on',+b.dataset.d===settings.dur)); }
function applySound(){ const t=audio.on?'🔊 الصوت شغّال':'🔇 الصوت مقفول'; $('btnSound').textContent=t; $('btnPauseSound').textContent=t; }
function updateStat(){ $('statLine').textContent=settings.played?('مباريات: '+settings.played+' · انتصارات: '+settings.wins+' · أفضل فارق: '+settings.best):'يلا نلعب كورة في الحارة!'; }
function toMenu(){
  detachInput(); mode='menu'; state='menu'; $('hud').classList.add('hidden'); delete $('results').dataset.shown;
  score=[0,0]; clock=settings.dur; for(const p of P){p.celebrate=false;} resetPositions(0,true); ball.x=0;ball.z=0;
  showOnly('menu'); updateStat(); applyDur(); applySound(); camS.init=false; audio.resume();
}
function startMatch(){
  audio.init(); audio.resume(); detachInput(); delete $('results').dataset.shown;
  mode='match'; style=0; updateStyle(); score=[0,0]; clock=settings.dur; matchDur=settings.dur; simTime=0; acc=0; pendingSay=null; bubbleCD=0; lineCD={};
  for(const b of bub){b.t=0;b.el.style.display='none';}
  for(const s of specs){s.react=0;s.type='';}
  resetPositions(0,true); state='countdown'; cdT=3.6; $('cdText').dataset.v=''; $('goalText').classList.remove('show');
  showOnly(''); $('hud').classList.remove('hidden'); updateHud(true); attachInput(); camS.init=false; if(quality.level<2) {}
  audio.whistle(false);
}
let matchDur=120;
function pauseGame(){
  if(mode!=='match'||state==='paused'||state==='menu'||state==='over') return;
  pausedFrom=state; state='paused'; showOnly('pause'); applySound(); audio.suspend();
  input.jx=input.jy=0; input.sprint=false; input.shootHeld=false; input.shootRel=false; input.charge=0; kb.l=kb.r=kb.u=kb.d=kb.s=0;
}
function resumeGame(){ if(state!=='paused') return; state=pausedFrom; showOnly(''); audio.resume(); lastT=0; }

/* ---------- input (attached on match start, aborted on exit) ---------- */
function detachInput(){ if(inputAC){ inputAC.abort(); inputAC=null; } input.jx=input.jy=0; input.sprint=input.shootHeld=input.shootRel=input.passQ=false; input.charge=0; kb.l=kb.r=kb.u=kb.d=kb.s=0; }
function attachInput(){
  inputAC=new AbortController(); const o={signal:inputAC.signal,passive:false};
  const zone=$('joyZone'),base=$('joyBase'),knob=$('joyKnob'); let jid=null,ox=0,oy=0; const R=58;
  function reset(){ jid=null; input.jx=input.jy=0; knob.style.transform=''; base.classList.remove('on'); base.style.left='';base.style.top='';base.style.bottom=''; }
  function upd(e){ let dx=e.clientX-ox,dy=e.clientY-oy,m=Math.hypot(dx,dy); if(m>R){dx=dx/m*R;dy=dy/m*R;m=R;}
    knob.style.transform='translate('+dx+'px,'+dy+'px)'; const mag=m/R;
    if(mag<0.12){input.jx=input.jy=0;}else{const k=(mag-0.12)/0.88;input.jx=dx/m*k;input.jy=dy/m*k;} }
  zone.addEventListener('pointerdown',e=>{ if(jid!==null) return; jid=e.pointerId; try{zone.setPointerCapture(jid);}catch(_){} ox=e.clientX;oy=e.clientY;
    base.style.left=(ox-65)+'px'; base.style.top=(oy-65)+'px'; base.style.bottom='auto'; base.classList.add('on'); upd(e); e.preventDefault(); },o);
  zone.addEventListener('pointermove',e=>{ if(e.pointerId!==jid) return; upd(e); e.preventDefault(); },o);
  const end=e=>{ if(e.pointerId===jid) reset(); };
  zone.addEventListener('pointerup',end,o); zone.addEventListener('pointercancel',end,o); zone.addEventListener('lostpointercapture',end,o);
  function hold(el,down,up){ let pid=null;
    el.addEventListener('pointerdown',e=>{ if(pid!==null) return; pid=e.pointerId; try{el.setPointerCapture(pid);}catch(_){} el.classList.add('down'); down(); e.preventDefault(); },o);
    const rel=e=>{ if(e.pointerId!==pid) return; pid=null; el.classList.remove('down'); up(); };
    el.addEventListener('pointerup',rel,o); el.addEventListener('pointercancel',rel,o); el.addEventListener('lostpointercapture',rel,o); }
  hold($('bPass'),()=>{input.passQ=true;},()=>{});
  hold($('bShoot'),()=>{input.shootHeld=true;},()=>{ if(input.shootHeld){input.shootHeld=false;input.shootRel=true;} });
  hold($('bSprint'),()=>{input.sprint=true;},()=>{input.sprint=false;});
  window.addEventListener('keydown',e=>{
    const c=e.code; let h=true;
    if(c==='ArrowLeft'||c==='KeyA')kb.l=1; else if(c==='ArrowRight'||c==='KeyD')kb.r=1; else if(c==='ArrowUp'||c==='KeyW')kb.u=1; else if(c==='ArrowDown'||c==='KeyS')kb.d=1;
    else if(c==='ShiftLeft'||c==='ShiftRight')kb.s=1;
    else if(c==='Space'||c==='KeyZ'){ if(!e.repeat) input.passQ=true; }
    else if(c==='KeyX'||c==='KeyK'){ if(!e.repeat) input.shootHeld=true; }
    else if(c==='KeyP'||c==='Escape'){ if(!e.repeat){ if(state==='paused') resumeGame(); else pauseGame(); } }
    else h=false;
    if(h) e.preventDefault();
  },o);
  window.addEventListener('keyup',e=>{
    const c=e.code;
    if(c==='ArrowLeft'||c==='KeyA')kb.l=0; else if(c==='ArrowRight'||c==='KeyD')kb.r=0; else if(c==='ArrowUp'||c==='KeyW')kb.u=0; else if(c==='ArrowDown'||c==='KeyS')kb.d=0;
    else if(c==='ShiftLeft'||c==='ShiftRight')kb.s=0;
    else if(c==='KeyX'||c==='KeyK'){ if(input.shootHeld){input.shootHeld=false;input.shootRel=true;} }
  },o);
  window.addEventListener('blur',()=>{ pauseGame(); },o);
  document.addEventListener('touchmove',e=>e.preventDefault(),o);
  document.addEventListener('contextmenu',e=>e.preventDefault(),o);
}

/* ---------- main loop (single rAF) ---------- */
function frame(t){
  rafId=requestAnimationFrame(frame);
  if(!lastT){ lastT=t; return; }
  let dt=(t-lastT)/1000; lastT=t; dt=Math.min(dt,0.1);
  if(state!=='paused'){
    if(mode==='match'){ acc+=dt; let n=0; while(acc>=STEP&&n<6){ step(STEP); acc-=STEP; n++; } if(n>=6) acc=0; }
    else{ simTime+=dt; for(const p of P){ steer(p,0,0,dt,10); } }
    syncVisuals(dt); updateCamera(dt); camera.updateMatrixWorld(); updateBubbles(dt); if(mode==='match') updateHud(false);
    adapt(dt);
  }
  renderer.render(scene,camera);
}
document.addEventListener('visibilitychange',()=>{ if(document.hidden){ pauseGame(); audio.suspend(); } else { lastT=0; if(state!=='paused') audio.resume(); } });

/* ---------- init ---------- */
async function init(){
  setProg(0.12,'جاري تجهيز الرسوميات…');
  try{ renderer=new THREE.WebGLRenderer({canvas:$('gl'),antialias:true,powerPreference:'high-performance'}); }
  catch(e){ showError('الجهاز أو المتصفح ما بيدعمش WebGL. جرّب Chrome محدّث. / WebGL is not available on this device.'); return; }
  quality.pr=Math.min(window.devicePixelRatio||1,isTouch?1.5:2);
  renderer.shadowMap.enabled=true; renderer.shadowMap.type=THREE.PCFSoftShadowMap;
  scene=new THREE.Scene(); scene.background=makeSky(); scene.fog=new THREE.Fog(0xc99a78,50,135);
  camera=new THREE.PerspectiveCamera(60,1,0.5,220); tmpV=new THREE.Vector3(); initGeo(); resize();
  await nextFrame(); setProg(0.25,'الأرض والملعب…'); buildLights(); buildGround(); buildGoals();
  await nextFrame(); setProg(0.45,'عمارات الحارة…'); buildEnvironment();
  await nextFrame(); setProg(0.7,'العربيات والسور والكشافات…'); buildCars(); buildCage(); buildFloodlights(); buildGraffiti(); buildFX(); buildBall();
  await loadRealAssets(); buildPlayers(); buildSpectators();
  document.querySelectorAll('.bubble').forEach(el=>bub.push({el,t:0,target:null}));
  await nextFrame(); setProg(0.92,'تجهيز القوائم…');
  wireUI(); window.addEventListener('resize',resize); window.addEventListener('orientationchange',()=>setTimeout(resize,200));
  resetPositions(0,true); clock=settings.dur;
  renderer.compile(scene,camera);
  $('loading').classList.add('hidden'); booted=true; toMenu(); setProg(1);
  if(rafId) cancelAnimationFrame(rafId); rafId=requestAnimationFrame(frame);
  window.__SK={step:step,startMatch:startMatch,state:()=>({state,mode,score:score.slice(),clock}),P:P,ball:ball,pause:pauseGame,resume:resumeGame,toMenu:toMenu,input:input};
}
function wireUI(){
  const tap=(id,fn)=>$(id).addEventListener('click',e=>{ e.preventDefault(); audio.init(); audio.resume(); fn(); });
  tap('btnPlay',startMatch);
  tap('btnHow',()=>showOnly('tutorial')); tap('btnHowClose',()=>showOnly('menu'));
  const snd=()=>{ audio.setOn(!audio.on); settings.sound=audio.on; store.set('sound',settings.sound); applySound(); };
  tap('btnSound',snd); tap('btnPauseSound',snd);
  document.querySelectorAll('#durSeg button').forEach(b=>b.addEventListener('click',()=>{ settings.dur=+b.dataset.d; store.set('dur',settings.dur); applyDur(); }));
  tap('btnResume',resumeGame); tap('btnRestart',startMatch); tap('btnPauseMenu',toMenu);
  tap('btnRematch',startMatch); tap('btnResMenu',toMenu);
  $('btnPause').addEventListener('pointerdown',e=>{ e.preventDefault(); e.stopPropagation(); pauseGame(); });
}
boot();
})();
