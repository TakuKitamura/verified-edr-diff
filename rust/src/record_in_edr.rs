use once_cell::sync::Lazy;
use std::sync::Mutex;

use chrono::prelude::*;
use chrono::Duration;
use std::fs;
use std::fs::OpenOptions;
use std::io::prelude::*;

#[no_mangle]
pub extern "C" fn recordInEDR(
    can_id: u32,
    timestamp: u64,
    speed: u16,
    indicator: u8,
    door: u8,
) -> i32 {
    let speed_id = 0x1b4;
    let indicator_id = 0x188;
    let door_id = 0x19b;

    struct EventData {
        timestamp: chrono::NaiveDateTime,
        crashed: bool,
        can_id: u32,
        speed: f64,
        indicator: u8,
        door: u8,
    }
    static STATIC_EVENT_DATA: Lazy<Mutex<Vec<EventData>>> = Lazy::new(|| Mutex::new(Vec::new()));

    let mut event_data = STATIC_EVENT_DATA.lock().unwrap();

    let sec_part: u64 = timestamp / 1000000; // 整数部

    // microsecondをnanosecondに変換
    let nano_part: u64 = (timestamp - (sec_part * 1000000)) * 1000; // 小数部
    let timestamp = NaiveDateTime::from_timestamp(sec_part as i64, nano_part as u32);

    let mut crashed_index: i32 = -1;
    match event_data.iter().position(|x| x.crashed == true) {
        None => (),
        Some(i) => {
            crashed_index = i as i32;
        }
    };

    let crashed = crashed_index != -1;

    if can_id == speed_id {
        // speed
        // 0x10で割る前の値がspeedなので0x10で割る
        let mph_speed: f64 = (speed as f64) / (0x10 as f64);

        event_data.push(EventData {
            can_id: can_id,
            timestamp: timestamp,
            crashed: crashed,
            speed: mph_speed,
            indicator: 0,
            door: 0,
        });

        let last_item_index = event_data.len() - 1;

        let now_speed = event_data[last_item_index].speed;

        let mut before_speed: f64 = now_speed;

        for i in (0..last_item_index).rev() {
            if event_data[i].can_id == speed_id {
                // speed
                before_speed = event_data[i].speed;
                break;
            }
        }

        let speed_delta: f64 = now_speed - before_speed;

        // TODO: 衝突と判定する速度変化を決める
        if speed_delta.abs() >= 1.0 && event_data[last_item_index].crashed == false {
            println!("crashed!!!!!");
            event_data[last_item_index].crashed = true;
        }
    } else if can_id == indicator_id {
        // indicator
        event_data.push(EventData {
            can_id: can_id,
            timestamp: timestamp,
            crashed: crashed,
            speed: 0.0,
            indicator: indicator,
            door: 0,
        });
    } else if can_id == door_id {
        // door
        event_data.push(EventData {
            can_id: can_id,
            timestamp: timestamp,
            crashed: crashed,
            speed: 0.0,
            indicator: 0,
            door: door,
        });
    } else {
        eprintln!("unknown id");
        return 2;
    }

    let mut index: i32 = 0;
    while index >= 0 && crashed == false {
        match event_data
            .iter()
            .position(|x| timestamp - x.timestamp > Duration::seconds(5))
        {
            None => index = -1,
            Some(i) => {
                index = i as i32;
            }
        };
        if index != -1 {
            event_data.remove(index as usize);
        }
    }

    // EDRへ書き込み
    if crashed {
        let before_time = event_data[event_data.len() - 1].timestamp;

        let crash_timestamp = event_data[crashed_index as usize].timestamp;

        if before_time - crash_timestamp >= Duration::seconds(5) {
            let file_name = "edr.csv";
            let _ = fs::remove_file(file_name);
            let mut file = OpenOptions::new()
                .write(true)
                .append(true)
                .create_new(true)
                .open(file_name)
                .unwrap();

            if let Err(e) = writeln!(file, "TIMESTAMP,CRASHED,EVENT_NAME,VALUE") {
                eprintln!("couldn't write to file: {}", e);
                return 2;
            }

            // loop event_data
            for i in 0..event_data.len() {
                let event_can_id = event_data[i].can_id;
                let timestamp =
                    DateTime::<Utc>::from_utc(event_data[i].timestamp, Utc).format("%+");
                // speed
                if let Err(e) = writeln!(
                    file,
                    "{},{},{},{}",
                    timestamp,
                    event_data[i].crashed,
                    if event_can_id == speed_id {
                        "SPEED"
                    } else if event_can_id == indicator_id {
                        "INDICATOR"
                    } else {
                        "DOOR"
                    },
                    if event_can_id == speed_id {
                        event_data[i].speed.to_string()
                    } else if event_can_id == indicator_id {
                        event_data[i].indicator.to_string()
                    } else {
                        event_data[i].door.to_string()
                    },
                ) {
                    eprintln!("couldn't write speed data to file: {}", e);
                    return 2;
                }
            }
            return 1;
        }
    }

    return 0;
}
