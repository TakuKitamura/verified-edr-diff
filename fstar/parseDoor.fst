module ParseDoor

open LowStar.BufferOps
open FStar.HyperStack.ST
open C.String
open FStar.Int.Cast
open HardCoding

module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module B = LowStar.Buffer

val parseDoor_body:
  can_id: U32.t ->
  can_dlc: U8.t ->
  data: B.buffer U8.t ->
  
Stack fstar_uint8 (requires fun h0 -> 
    B.live h0 data /\ (((B.length data) = (8)) &&
    (U32.eq can_id 0x19Bul) &&
    (U8.eq can_dlc 6uy) &&
    (U8.eq (B.get h0 data 0) 0uy) &&
    (U8.eq (B.get h0 data 1) 0uy) &&
    (U8.lte (B.get h0 data 2) 0x0Fuy) &&
    (U8.eq (B.get h0 data 3) 0uy) &&
    (U8.eq (B.get h0 data 4) 0uy) &&
    (U8.eq (B.get h0 data 5) 0uy))
  )
  (ensures fun h0 fstar_uint8 h1 -> 
    (((I32.eq fstar_uint8.error.code 0l) &&
    ((B.get h0 data 2) = fstar_uint8.value) &&
    (U8.lte fstar_uint8.value 0x0Fuy)) ||
    (I32.eq fstar_uint8.error.code 1l))
  )
let parseDoor_body can_id can_dlc data  =
    let door_state: U8.t = data.(2ul) in
    let ret: U8.t = door_state in
    if (U8.eq door_state ret) then
        (
            {
                value = ret;
                error = {
                    code = 0l;
                    message = !$"";
                };
            }
        )
    else
        (
            {
                value = 1uy;
                error = {
                    code = 1l;
                    message = !$"invalid door state";
                };
            }
        )

val parseDoor: 
  can_id: U32.t ->
  can_dlc: U8.t ->
  data: B.buffer U8.t ->
  
  Stack fstar_uint8 (requires fun h0 -> 
    B.live h0 data /\ (((B.length data) = (8)))
  )
  (ensures fun h0 fstar_uint8 h1 -> 
    (((I32.eq fstar_uint8.error.code 0l) &&
    ((B.get h0 data 2) = fstar_uint8.value) &&
    (U8.lte fstar_uint8.value 0x0Fuy)) ||
    (I32.eq fstar_uint8.error.code 1l))
  )
let parseDoor can_id can_dlc data  = 
    // meet the preconditions
    if (let v1 = data.(0ul) in
    let v2 = data.(1ul) in
    let v3 = data.(2ul) in
    let v4 = data.(3ul) in
    let v5 = data.(4ul) in
    let v6 = data.(5ul) in
    ((U32.eq can_id 0x19Bul) &&
    (U8.eq can_dlc 6uy) &&
    (U8.eq v1 0uy) &&
    (U8.eq v2 0uy) &&
    (U8.lte v3 0x0Fuy) &&
    (U8.eq v4 0uy) &&
    (U8.eq v5 0uy) &&
    (U8.eq v6 0uy))) then
        parseDoor_body can_id can_dlc data 
    else
        {
            value = 0uy;
            error = {
                code = 1l;
                message = !$"invalid arguments";
            };
        }

