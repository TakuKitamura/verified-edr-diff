module ParseSpeed

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

val parseSpeed_body:
  can_id: U32.t ->
  can_dlc: U8.t ->
  data: B.buffer U8.t ->
  
Stack fstar_uint16 (requires fun h0 -> 
    B.live h0 data /\ (((B.length data) = (8)) &&
    (U32.eq can_id 0x1b4ul) &&
    (U8.eq can_dlc 5uy) &&
    (U8.gte (B.get h0 data 1) 0xD0uy) &&
    (U8.eq (B.get h0 data 2) 0uy) &&
    (U8.eq (B.get h0 data 3) 0uy) &&
    (U8.eq (B.get h0 data 4) 0uy))
  )
  (ensures fun h0 fstar_uint16 h1 -> 
    (((I32.eq fstar_uint16.error.code 0l) &&
    (U16.lte fstar_uint16.value 0x2fd0us)) ||
    (I32.eq fstar_uint16.error.code 1l))
  )
let parseSpeed_body can_id can_dlc data  =
    push_frame ();
    let first_speed_byte_u8: U8.t = data.(0ul) in
    let second_speed_byte_u8: U8.t = data.(1ul) in
    let first_speed_byte_u16: U16.t = uint8_to_uint16 first_speed_byte_u8 in
    let second_speed_byte_u16: U16.t = uint8_to_uint16 second_speed_byte_u8 in
    let ret: U16.t = U16.(
        ((second_speed_byte_u16 -^ 0xd0us) *^ 0xffus) +^ 
        first_speed_byte_u16
    ) in
    pop_frame ();
    {
        value = ret;
        error = {
            code = 0l;
            message = !$"";
        };
    } 

val parseSpeed: 
  can_id: U32.t ->
  can_dlc: U8.t ->
  data: B.buffer U8.t ->
  
  Stack fstar_uint16 (requires fun h0 -> 
    B.live h0 data /\ (((B.length data) = (8)))
  )
  (ensures fun h0 fstar_uint16 h1 -> 
    (((I32.eq fstar_uint16.error.code 0l) &&
    (U16.lte fstar_uint16.value 0x2fd0us)) ||
    (I32.eq fstar_uint16.error.code 1l))
  )
let parseSpeed can_id can_dlc data  = 
    if (let v1 = data.(1ul) in
    let v2 = data.(2ul) in
    let v3 = data.(3ul) in
    let v4 = data.(4ul) in
    ((U32.eq can_id 0x1b4ul) &&
    (U8.eq can_dlc 5uy) &&
    (U8.gte v1 0xD0uy) &&
    (U8.eq v2 0uy) &&
    (U8.eq v3 0uy) &&
    (U8.eq v4 0uy))) then
        parseSpeed_body can_id can_dlc data 
    else
        {
            value = 0us;
            error = {
            code = 1l;
                message = !$"invalid arguments";
            };
        }
