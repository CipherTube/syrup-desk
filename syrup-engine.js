/* syrup-engine.js — Twisted Syrup audio engine.
 * Pure Web Audio, no DOM. Runs in the browser and in Node (node-web-audio-api),
 * so the exact graph that ships is the graph under test.
 *
 * Invariant taken from the spec: nothing that makes sound sits in series with
 * the output path. Meters only listen. That was the silent-output bug.
 */

(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.SyrupEngine = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  var PRESETS = {
    reign: {
      name: '806 Boss Thuggish Reign', bpm: 64, root: 48, scale: 'minor', screw: -4,
      progression: [0, 0, 5, 5, 3, 3, 4, 4],
      lanes: {
        kick:  [[0, 1.0], [8, 0.95]],
        snare: [[4, 0.9]],
        hat:   [[0, 0.5], [3, 0.4], [6, 0.45], [9, 0.5], [12, 0.4], [14, 0.45]],
        chop:  [[2, 0.6], [10, 0.55], [13, 0.5]]
      },
      sections: [{ bars: 8, mode: 'intro' }, { bars: 16, mode: 'heavy' }, { bars: 2, mode: 'screwcut' }]
    },
    anchor: {
      name: 'West Texas Anchor', bpm: 62, root: 43, scale: 'minor', screw: -5,
      progression: [0, 0, 3, 3, 5, 5, 0, 0],
      lanes: {
        kick:  [[0, 1.0], [7, 0.85]],
        snare: [[8, 0.95]],
        hat:   [[0, 0.45], [2, 0.4], [5, 0.4], [8, 0.45], [11, 0.4], [14, 0.4]],
        chop:  [[1, 0.55], [9, 0.6]]
      },
      sections: [{ bars: 8, mode: 'intro' }, { bars: 20, mode: 'heavy' }, { bars: 2, mode: 'screwcut' }]
    },
    dragon: {
      name: 'Chasing the Dragon Passing Past Cloud 9', bpm: 60, root: 46, scale: 'dorian', screw: -3,
      progression: [0, 4, 5, 4, 0, 4, 3, 3],
      lanes: {
        kick:  [[0, 0.95]],
        snare: [[8, 0.85]],
        hat:   [[0, 0.4], [3, 0.35], [6, 0.35], [9, 0.4], [12, 0.35], [15, 0.35]],
        chop:  [[2, 0.6], [11, 0.55]]
      },
      sections: [{ bars: 12, mode: 'intro' }, { bars: 16, mode: 'heavy' }, { bars: 2, mode: 'screwcut' }]
    },
    upload: {
      name: 'Upload & Download', bpm: 66, root: 41, scale: 'minor', screw: -4,
      progression: [0, 3, 0, 3, 5, 5, 4, 4],
      lanes: {
        kick:  [[0, 1.0], [6, 0.85], [10, 0.8]],
        snare: [[4, 0.9], [12, 0.85]],
        hat:   [[0, 0.4], [2, 0.35], [4, 0.45], [7, 0.35], [9, 0.4], [12, 0.45], [14, 0.35]],
        chop:  [[3, 0.55], [8, 0.6], [13, 0.55]]
      },
      sections: [{ bars: 8, mode: 'intro' }, { bars: 24, mode: 'heavy' }, { bars: 2, mode: 'screwcut' }]
    }
  };

  var SCALES = { minor: [0, 2, 3, 5, 7, 8, 10], dorian: [0, 2, 3, 5, 7, 9, 10] };

  function midiToFreq(m) { return 440 * Math.pow(2, (m - 69) / 12); }
  function clamp(v, lo, hi) { return v < lo ? lo : v > hi ? hi : v; }
  function deepCopy(o) { return JSON.parse(JSON.stringify(o)); }

  function softClipCurve(amount, n) {
    n = n || 2048;
    var curve = new Float32Array(n);
    var k = Math.max(0.001, amount);
    var norm = Math.tanh(k);
    for (var i = 0; i < n; i++) {
      var x = (i / (n - 1)) * 2 - 1;
      curve[i] = Math.tanh(x * k) / norm;
    }
    return curve;
  }

  function makeNoise(ctx, seconds) {
    var len = Math.max(1, Math.floor(ctx.sampleRate * seconds));
    var buf = ctx.createBuffer(1, len, ctx.sampleRate);
    var d = buf.getChannelData(0);
    var seed = 22222;
    for (var i = 0; i < len; i++) {
      seed = (seed * 1103515245 + 12345) & 0x7fffffff;
      d[i] = (seed / 0x3fffffff) - 1;
    }
    return buf;
  }

  function makeImpulse(ctx, seconds, decay) {
    var len = Math.max(1, Math.floor(ctx.sampleRate * seconds));
    var buf = ctx.createBuffer(2, len, ctx.sampleRate);
    for (var ch = 0; ch < 2; ch++) {
      var d = buf.getChannelData(ch);
      var seed = ch === 0 ? 9871 : 4483;
      var prev = 0;
      for (var i = 0; i < len; i++) {
        seed = (seed * 1103515245 + 12345) & 0x7fffffff;
        var white = (seed / 0x3fffffff) - 1;
        prev = prev * 0.72 + white * 0.28;          // dark, murky tail
        var t = i / len;
        d[i] = prev * Math.pow(1 - t, decay);
      }
    }
    return buf;
  }

  function createSyrup(ctx, options) {
    options = options || {};
    var engine = {};
    var bank = deepCopy(PRESETS);
    var current = options.preset && bank[options.preset] ? options.preset : 'reign';

    var state = {
      preset: current,
      playing: false,
      bar: 0,
      loop: false,
      bpm: bank[current].bpm,
      screw: bank[current].screw,
      glideMs: 96,
      headroom: 0.72,
      timer: null,
      nextBarTime: 0
    };

    // ---------------- master path: everything -> turntable -> master -> out
    var turntable = ctx.createBiquadFilter();
    turntable.type = 'lowpass';
    turntable.frequency.value = 19000;
    turntable.Q.value = 0.0001;

    var master = ctx.createGain();
    master.gain.value = state.headroom;

    var limiter = ctx.createDynamicsCompressor();
    limiter.threshold.value = -4;
    limiter.knee.value = 0;
    limiter.ratio.value = 20;
    limiter.attack.value = 0.002;
    limiter.release.value = 0.12;

    turntable.connect(master);
    master.connect(limiter);
    limiter.connect(ctx.destination);

    // meter: tapped, never in series
    var analyser = ctx.createAnalyser();
    analyser.fftSize = 2048;
    analyser.smoothingTimeConstant = 0.6;
    master.connect(analyser);

    function bus(gain) {
      var g = ctx.createGain();
      g.gain.value = gain;
      g.connect(turntable);
      return g;
    }
    var drumsBus = bus(0.9);
    var subBus = bus(1.0);
    var melodyBus = bus(0.5);
    var chopBus = bus(0.55);

    // ---------------- cavernous wash (aux return, 100% wet)
    var washInput = ctx.createGain();
    var preDelay = ctx.createDelay(0.5);
    preDelay.delayTime.value = 0.06;
    var cavern = ctx.createConvolver();
    cavern.buffer = makeImpulse(ctx, 6.5, 2.4);
    var cavernReturn = ctx.createGain();
    cavernReturn.gain.value = 0.6;
    washInput.connect(preDelay);
    preDelay.connect(cavern);
    cavern.connect(cavernReturn);
    cavernReturn.connect(turntable);

    var delayL = ctx.createDelay(3);
    var delayR = ctx.createDelay(3);
    var feedback = ctx.createGain();
    var damp = ctx.createBiquadFilter();
    var delayReturn = ctx.createGain();
    var panL = ctx.createStereoPanner();
    var panR = ctx.createStereoPanner();
    feedback.gain.value = 0.52;
    damp.type = 'lowpass';
    damp.frequency.value = 1900;
    delayReturn.gain.value = 0.4;
    panL.pan.value = -0.8;
    panR.pan.value = 0.8;
    washInput.connect(delayL);
    washInput.connect(delayR);
    delayL.connect(panL);
    delayR.connect(panR);
    panL.connect(delayReturn);
    panR.connect(delayReturn);
    delayReturn.connect(turntable);
    delayL.connect(damp);
    damp.connect(feedback);
    feedback.connect(delayL);
    feedback.connect(delayR);

    function sendToWash(node, amount) {
      var s = ctx.createGain();
      s.gain.value = amount;
      node.connect(s);
      s.connect(washInput);
      return s;
    }

    // ---------------- 808: mono glide, soft clip, 120 Hz ceiling
    var subShaper = ctx.createWaveShaper();
    subShaper.curve = softClipCurve(2.6);
    subShaper.oversample = '4x';
    var subFilter = ctx.createBiquadFilter();
    subFilter.type = 'lowpass';
    subFilter.frequency.value = 120;
    subFilter.Q.value = 0.7;
    var subGate = ctx.createGain();       // sidechain target
    subGate.gain.value = 1;
    subShaper.connect(subFilter);
    subFilter.connect(subGate);
    subGate.connect(subBus);

    var subPrevFreq = 0;

    function playSub(freq, time, dur, velocity) {
      var osc = ctx.createOscillator();
      var env = ctx.createGain();
      var target = freq * Math.pow(2, state.screw / 12);
      osc.type = 'sine';
      if (subPrevFreq > 0) {
        osc.frequency.setValueAtTime(subPrevFreq, time);
        osc.frequency.exponentialRampToValueAtTime(target, time + state.glideMs / 1000);
      } else {
        osc.frequency.setValueAtTime(target, time);
      }
      subPrevFreq = target;
      var v = clamp(velocity == null ? 0.9 : velocity, 0.05, 1);
      var hold = Math.max(0.3, dur);
      env.gain.setValueAtTime(0.0001, time);
      env.gain.exponentialRampToValueAtTime(v, time + 0.012);
      env.gain.exponentialRampToValueAtTime(0.0001, time + hold);
      osc.connect(env);
      env.connect(subShaper);
      osc.start(time);
      osc.stop(time + hold + 0.06);
    }

    // ---------------- drums
    var noiseBuf = makeNoise(ctx, 2);

    function playKick(time, velocity) {
      var osc = ctx.createOscillator();
      var env = ctx.createGain();
      var lp = ctx.createBiquadFilter();
      lp.type = 'lowpass';
      lp.frequency.value = 4000;
      osc.type = 'sine';
      osc.frequency.setValueAtTime(150, time);
      osc.frequency.exponentialRampToValueAtTime(44, time + 0.08);
      var v = clamp(velocity == null ? 1 : velocity, 0.05, 1);
      env.gain.setValueAtTime(0.0001, time);
      env.gain.exponentialRampToValueAtTime(0.95 * v, time + 0.006);
      env.gain.exponentialRampToValueAtTime(0.0001, time + 0.5);
      osc.connect(env);
      env.connect(lp);
      lp.connect(drumsBus);
      osc.start(time);
      osc.stop(time + 0.6);

      var g = subGate.gain;
      g.cancelScheduledValues(time);
      g.setValueAtTime(0.3, time);
      g.linearRampToValueAtTime(1, time + 0.16);
    }

    function playSnare(time, velocity) {
      var src = ctx.createBufferSource();
      src.buffer = noiseBuf;
      var bp = ctx.createBiquadFilter();
      bp.type = 'bandpass';
      bp.frequency.value = 1750;
      bp.Q.value = 0.9;
      var env = ctx.createGain();
      var v = clamp(velocity == null ? 0.9 : velocity, 0.05, 1);
      env.gain.setValueAtTime(0.0001, time);
      env.gain.exponentialRampToValueAtTime(0.7 * v, time + 0.004);
      env.gain.exponentialRampToValueAtTime(0.0001, time + 0.26);
      src.connect(bp);
      bp.connect(env);
      env.connect(drumsBus);
      sendToWash(env, 0.4);
      src.start(time);
      src.stop(time + 0.3);
    }

    function playHat(time, velocity, rate) {
      var src = ctx.createBufferSource();
      src.buffer = noiseBuf;
      src.playbackRate.value = rate || 1.4;
      var hp = ctx.createBiquadFilter();
      hp.type = 'highpass';
      hp.frequency.value = 7000;
      var env = ctx.createGain();
      var v = clamp(velocity == null ? 0.4 : velocity, 0.05, 1);
      env.gain.setValueAtTime(0.0001, time);
      env.gain.exponentialRampToValueAtTime(0.26 * v, time + 0.003);
      env.gain.exponentialRampToValueAtTime(0.0001, time + 0.07);
      src.connect(hp);
      hp.connect(env);
      env.connect(drumsBus);
      src.start(time);
      src.stop(time + 0.09);
    }

    // ---------------- pads and chops
    function playPad(freqs, time, dur, velocity) {
      var env = ctx.createGain();
      var lp = ctx.createBiquadFilter();
      var hp = ctx.createBiquadFilter();
      lp.type = 'lowpass';
      lp.frequency.setValueAtTime(650, time);
      lp.frequency.linearRampToValueAtTime(1600, time + dur * 0.7);
      lp.Q.value = 0.5;
      hp.type = 'highpass';
      hp.frequency.value = 250;
      var v = clamp(velocity == null ? 0.5 : velocity, 0.05, 1);
      var oscs = [];
      freqs.forEach(function (f, i) {
        var o = ctx.createOscillator();
        o.type = i === 0 ? 'triangle' : 'sawtooth';
        o.frequency.value = f * Math.pow(2, state.screw / 12);
        o.detune.value = (i - 1) * 7;
        o.connect(lp);
        o.start(time);
        o.stop(time + dur + 0.05);
        oscs.push(o);
      });
      env.gain.setValueAtTime(0.0001, time);
      env.gain.linearRampToValueAtTime(0.2 * v, time + Math.min(0.6, dur * 0.3));
      env.gain.linearRampToValueAtTime(0.0001, time + dur);
      lp.connect(hp);
      hp.connect(env);
      env.connect(melodyBus);
      sendToWash(env, 0.42);
    }

    function playChop(freq, time, velocity) {
      var osc = ctx.createOscillator();
      var env = ctx.createGain();
      var bp = ctx.createBiquadFilter();
      bp.type = 'bandpass';
      bp.frequency.value = freq * 2.2;
      bp.Q.value = 5;
      osc.type = 'sawtooth';
      osc.frequency.value = freq * Math.pow(2, state.screw / 12);
      var v = clamp(velocity == null ? 0.5 : velocity, 0.05, 1);
      env.gain.setValueAtTime(0.0001, time);
      env.gain.exponentialRampToValueAtTime(0.5 * v, time + 0.01);
      env.gain.exponentialRampToValueAtTime(0.0001, time + 0.22);
      osc.connect(bp);
      bp.connect(env);
      env.connect(chopBus);
      sendToWash(env, 0.7);
      osc.start(time);
      osc.stop(time + 0.26);
    }

    // ---------------- musical helpers
    function chordForBar(bar) {
      var p = bank[state.preset];
      var scale = SCALES[p.scale] || SCALES.minor;
      var degree = p.progression[bar % p.progression.length];
      var root = p.root + scale[degree % scale.length];
      var third = p.root + scale[(degree + 2) % scale.length] + (degree + 2 >= scale.length ? 12 : 0);
      var fifth = p.root + scale[(degree + 4) % scale.length] + (degree + 4 >= scale.length ? 12 : 0);
      return { root: root, third: third, fifth: fifth };
    }

    function sectionForBar(bar) {
      var p = bank[state.preset];
      var acc = 0;
      for (var i = 0; i < p.sections.length; i++) {
        acc += p.sections[i].bars;
        if (bar < acc) return p.sections[i].mode;
      }
      return 'heavy';
    }

    function totalBars() {
      return bank[state.preset].sections.reduce(function (a, s) { return a + s.bars; }, 0);
    }

    function barSeconds() {
      var bpm = state.bpm * Math.pow(2, state.screw / 12);
      return (60 / bpm) * 4;
    }

    // ---------------- one bar of music
    function scheduleBar(bar, t0) {
      var p = bank[state.preset];
      var chord = chordForBar(bar);
      var mode = sectionForBar(bar);
      var barLen = barSeconds();
      var stepDur = barLen / 16;
      var heavy = mode === 'heavy' || mode === 'screwcut';

      playPad([midiToFreq(chord.root), midiToFreq(chord.third), midiToFreq(chord.fifth)], t0, barLen * 0.98, 0.55);

      (p.lanes.chop || []).forEach(function (e) {
        playChop(midiToFreq(chord.root + 12), t0 + e[0] * stepDur, e[1] * 0.8);
      });

      if (mode === 'screwcut') {
        tapeStop(t0, 0.55);
        stutter(t0 + barLen * 0.5, stepDur);
      }

      if (!heavy) return;

      (p.lanes.kick || []).forEach(function (e) {
        playKick(t0 + e[0] * stepDur, e[1]);
      });
      (p.lanes.snare || []).forEach(function (e) {
        playSnare(t0 + e[0] * stepDur, e[1]);
      });
      // triplet hats: three quick strokes per written step
      (p.lanes.hat || []).forEach(function (e) {
        var at = t0 + e[0] * stepDur;
        playHat(at, e[1], 1.5);
        playHat(at + stepDur / 3, e[1] * 0.75, 1.65);
        playHat(at + (2 * stepDur) / 3, e[1] * 0.6, 1.8);
      });

      // 808: root on the first kick, fifth halfway through the bar, gliding
      playSub(midiToFreq(chord.root - 12), t0, stepDur * 7, 0.95);
      playSub(midiToFreq(chord.fifth - 12), t0 + stepDur * 8, stepDur * 6, 0.85);
    }

    // ---------------- turntable mechanics
    function tapeStop(when, seconds) {
      var t = when == null ? ctx.currentTime : when;
      var d = seconds || 0.5;
      var f = turntable.frequency;
      f.cancelScheduledValues(t);
      f.setValueAtTime(Math.max(200, f.value), t);
      f.exponentialRampToValueAtTime(90, t + d);
      f.setValueAtTime(19000, t + d + 0.01);
    }

    function stutter(when, stepDur) {
      var t = when == null ? ctx.currentTime : when;
      var slice = Math.max(0.05, stepDur || 0.12);
      for (var i = 0; i < 4; i++) {
        playHat(t + i * slice * 0.5, 0.5 - i * 0.08, 2.0);
        if (i % 2 === 0) playSnare(t + i * slice * 0.5, 0.35 - i * 0.05);
      }
    }

    function setScrew(semitones) {
      state.screw = clamp(semitones, -12, 12);
      return state.screw;
    }

    function setBpm(bpm) {
      state.bpm = clamp(bpm, 60, 68);
      return state.bpm;
    }

    // ---------------- transport
    function scheduleAhead() {
      if (!state.playing) return;
      var horizon = ctx.currentTime + 0.6;
      var guard = 0;
      while (state.nextBarTime < horizon && guard < 8) {
        var bar = state.bar;
        scheduleBar(bar, state.nextBarTime);
        state.nextBarTime += barSeconds();
        state.bar = bar + 1;
        if (state.bar >= totalBars()) state.bar = 0;   // loop the arrangement
        guard++;
      }
    }

    function start(when) {
      if (state.playing) return;
      state.playing = true;
      state.bar = 0;
      subPrevFreq = 0;
      state.nextBarTime = when == null ? ctx.currentTime + 0.08 : when;
      scheduleAhead();
      state.timer = setInterval(scheduleAhead, 120);
      return state.nextBarTime;
    }

    function stop() {
      state.playing = false;
      if (state.timer) { clearInterval(state.timer); state.timer = null; }
    }

    function setPreset(name) {
      if (!bank[name]) return state.preset;
      state.preset = name;
      state.bpm = bank[name].bpm;
      state.screw = bank[name].screw;
      state.bar = 0;
      subPrevFreq = 0;
      return name;
    }

    function paint(lane, step, velocity) {
      var p = bank[state.preset];
      if (!p.lanes[lane]) p.lanes[lane] = [];
      var arr = p.lanes[lane];
      arr = arr.filter(function (e) { return e[0] !== step; });
      if (velocity > 0) arr.push([step, velocity]);
      arr.sort(function (a, b) { return a[0] - b[0]; });
      p.lanes[lane] = arr;
      return arr;
    }

    function testTone(seconds) {
      var t = ctx.currentTime + 0.02;
      var osc = ctx.createOscillator();
      var env = ctx.createGain();
      osc.type = 'sine';
      osc.frequency.setValueAtTime(midiToFreq(57), t);
      env.gain.setValueAtTime(0.0001, t);
      env.gain.exponentialRampToValueAtTime(0.5, t + 0.02);
      env.gain.exponentialRampToValueAtTime(0.0001, t + (seconds || 0.8));
      osc.connect(env);
      env.connect(master);
      osc.start(t);
      osc.stop(t + (seconds || 0.8) + 0.05);
    }

    function nowPlayingTime() {
      var p = bank[state.preset];
      var sec = barSeconds();
      return { bar: state.bar, section: sectionForBar(state.bar), step: 0, barSeconds: sec, preset: p.name };
    }

    // expose internals the UI and the tests both need
    engine.ctx = ctx;
    engine.state = state;
    engine.presets = bank;
    engine.master = master;
    engine.analyser = analyser;
    engine.buses = { drums: drumsBus, sub: subBus, melody: melodyBus, chop: chopBus, wash: washInput };
    engine.start = start;
    engine.stop = stop;
    engine.setPreset = setPreset;
    engine.setBpm = setBpm;
    engine.setScrew = setScrew;
    engine.paint = paint;
    engine.tapeStop = tapeStop;
    engine.stutter = stutter;
    engine.testTone = testTone;
    engine.nowPlayingTime = nowPlayingTime;
    engine.scheduleBar = scheduleBar;
    engine.totalBars = totalBars;
    engine.barSeconds = barSeconds;
    engine.chordForBar = chordForBar;
    engine.sectionForBar = sectionForBar;

    /* Render the arrangement offline, exactly as it plays live. */
    engine.renderBarRange = function (makeContext, fromBar, bars, sampleRate) {
      var sr = sampleRate || 44100;
      var secPerBar = barSeconds();
      var seconds = bars * secPerBar + 3.5;
      var off = makeContext(Math.ceil(sr * seconds), sr);
      var inner = createSyrup(off, { preset: state.preset });
      inner.state.bpm = state.bpm;
      inner.state.screw = state.screw;
      for (var b = 0; b < bars; b++) {
        inner.scheduleBar(fromBar + b, 0.05 + b * inner.barSeconds());
      }
      return off.startRendering();
    };

    return engine;
  }

  return {
    createSyrup: createSyrup,
    PRESETS: PRESETS,
    SCALES: SCALES,
    midiToFreq: midiToFreq
  };
});
