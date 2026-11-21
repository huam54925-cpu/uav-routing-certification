import LeanCompletion.UAV.TreeBudgetColumnCheckRuns

namespace UAVProof.A4ColumnCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition

set_option synthInstance.maxSize 4096
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def root_le (d : Data) (ha : d.reg .a=[]) (hb : d.reg .b=[])
    (hc : d.reg .c=[]) (hd : d.reg .d=[]) (hs : d.reg .scratch=[]) :
    Run (cfg .rootA d) (cfg (if value (d.reg .index)≤value (d.reg .root) then .rootBackA else .records) d)
      (3*((d.reg .index).length+(d.reg .root).length)+9) := by
  let d1 := put d (wr .a) (d.reg .index)
  let d2 := put d1 (wr .b) (d.reg .root)
  have h1 : Run (cfg .rootA d) (cfg .rootB d1) (2*(d.reg .index).length+3) := by
    simpa only [store,ha,List.append_nil] using copyData .rootA .rootB _ rfl d hs
  have h2 : Run (cfg .rootB d1) (cfg .rootLe d2) (2*(d.reg .root).length+3) := by
    simpa [d1,store,put,Function.update_apply,hb] using copyData .rootB .rootLe _ rfl d1
      (by simp [d1,store,put,Function.update_apply,hs])
  have h3 := leData .rootLe .rootBackA .records rfl d2
    (by simp [d1,d2,put,Function.update_apply,hc])
    (by simp [d1,d2,put,Function.update_apply,hd])
  have he : put (put d2 (wr .a) []) (wr .b) []=d := by
    apply data_ext
    · rfl
    · funext r; cases r <;> simp [d1,d2,put,Function.update_apply,ha,hb]
  rw [he] at h3
  convert seq (seq h1 h2) h3 using 1 <;>
    simp [d1,d2,put,Function.update_apply] <;> omega

def root_ge (d : Data) (ha : d.reg .a=[]) (hb : d.reg .b=[])
    (hc : d.reg .c=[]) (hd : d.reg .d=[]) (hs : d.reg .scratch=[]) :
    Run (cfg .rootBackA d) (cfg (if value (d.reg .root)≤value (d.reg .index) then .clearTarget else .records) d)
      (3*((d.reg .root).length+(d.reg .index).length)+9) := by
  let d1 := put d (wr .a) (d.reg .root)
  let d2 := put d1 (wr .b) (d.reg .index)
  have h1 : Run (cfg .rootBackA d) (cfg .rootBackB d1) (2*(d.reg .root).length+3) := by
    simpa only [store,ha,List.append_nil] using copyData .rootBackA .rootBackB _ rfl d hs
  have h2 : Run (cfg .rootBackB d1) (cfg .rootBackLe d2) (2*(d.reg .index).length+3) := by
    simpa [d1,store,put,Function.update_apply,hb] using copyData .rootBackB .rootBackLe _ rfl d1
      (by simp [d1,store,put,Function.update_apply,hs])
  have h3 := leData .rootBackLe .clearTarget .records rfl d2
    (by simp [d1,d2,put,Function.update_apply,hc])
    (by simp [d1,d2,put,Function.update_apply,hd])
  have he : put (put d2 (wr .a) []) (wr .b) []=d := by
    apply data_ext
    · rfl
    · funext r; cases r <;> simp [d1,d2,put,Function.update_apply,ha,hb]
  rw [he] at h3
  convert seq (seq h1 h2) h3 using 1 <;>
    simp [d1,d2,put,Function.update_apply] <;> omega

def sum_le (d : Data) (ha : d.reg .a=[]) (hb : d.reg .b=[])
    (hc : d.reg .c=[]) (hd : d.reg .d=[]) (hs : d.reg .scratch=[]) :
    Run (cfg .sumA d) (cfg (if value (d.reg .acc)≤value (d.reg .target) then .sumBackB else .bad) d)
      (3*((d.reg .acc).length+(d.reg .target).length)+9) := by
  let d1 := put d (wr .a) (d.reg .acc)
  let d2 := put d1 (wr .b) (d.reg .target)
  have h1 : Run (cfg .sumA d) (cfg .sumLe d1) (2*(d.reg .acc).length+3) := by
    simpa only [store,ha,List.append_nil] using copyData .sumA .sumLe _ rfl d hs
  have h2 : Run (cfg .sumLe d1) (cfg .sumBackA d2) (2*(d.reg .target).length+3) := by
    simpa [d1,store,put,Function.update_apply,hb] using copyData .sumLe .sumBackA _ rfl d1
      (by simp [d1,store,put,Function.update_apply,hs])
  have h3 := leData .sumBackA .sumBackB .bad rfl d2
    (by simp [d1,d2,put,Function.update_apply,hc])
    (by simp [d1,d2,put,Function.update_apply,hd])
  have he : put (put d2 (wr .a) []) (wr .b) []=d := by
    apply data_ext
    · rfl
    · funext r; cases r <;> simp [d1,d2,put,Function.update_apply,ha,hb]
  rw [he] at h3
  convert seq (seq h1 h2) h3 using 1 <;>
    simp [d1,d2,put,Function.update_apply] <;> omega

def sum_ge (d : Data) (ha : d.reg .a=[]) (hb : d.reg .b=[])
    (hc : d.reg .c=[]) (hd : d.reg .d=[]) (hs : d.reg .scratch=[]) :
    Run (cfg .sumBackB d) (cfg (if value (d.reg .target)≤value (d.reg .acc) then .clearTarget else .bad) d)
      (3*((d.reg .target).length+(d.reg .acc).length)+9) := by
  let d1 := put d (wr .a) (d.reg .target)
  let d2 := put d1 (wr .b) (d.reg .acc)
  have h1 : Run (cfg .sumBackB d) (cfg .sumBackLe d1) (2*(d.reg .target).length+3) := by
    simpa only [store,ha,List.append_nil] using copyData .sumBackB .sumBackLe _ rfl d hs
  have h2 : Run (cfg .sumBackLe d1) (cfg .clearSum d2) (2*(d.reg .acc).length+3) := by
    simpa [d1,store,put,Function.update_apply,hb] using copyData .sumBackLe .clearSum _ rfl d1
      (by simp [d1,store,put,Function.update_apply,hs])
  have h3 := leData .clearSum .clearTarget .bad rfl d2
    (by simp [d1,d2,put,Function.update_apply,hc])
    (by simp [d1,d2,put,Function.update_apply,hd])
  have he : put (put d2 (wr .a) []) (wr .b) []=d := by
    apply data_ext
    · rfl
    · funext r; cases r <;> simp [d1,d2,put,Function.update_apply,ha,hb]
  rw [he] at h3
  convert seq (seq h1 h2) h3 using 1 <;>
    simp [d1,d2,put,Function.update_apply] <;> omega

end UAVProof.A4ColumnCheck
