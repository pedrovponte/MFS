abstract sig Landing_Set {
    door : one Door,
    landing_gear : one Landing_Gear,
    close_EV : one Electro_Valve,
    open_EV : one Electro_Valve,
    retract_EV : one Electro_Valve,
    extend_EV : one Electro_Valve
}

one sig Front, Right, Left extends Landing_Set {}

sig Door {
    var stateD : one Door_Status
}

sig Landing_Gear {
    var stateG : one Gear_Status
}

one sig Pilot_Handle {
    var position : one Handle_Position
}

sig Electro_Valve {
    var stateE : one Valve_State
}

abstract sig Door_Status {}

one sig Closed, Open extends Door_Status {}

abstract sig Gear_Status {}

one sig Retracted, Extended extends Gear_Status {}

abstract sig Handle_Position {}

one sig Up, Down extends Handle_Position {}

abstract sig Valve_State {}

one sig Stimulated, Unstimulated extends Valve_State {}

// Each landing set has its own door
fact DifferentDoors {
	// always (all l1, l2 : Landing_Set | l1.door = l2.door => l1 = l2)
}

// Each landing set has its own landing gear
fact DifferentGears {
	// always (all l1, l2 : Landing_Set | l1.landing_gear = l2.landing_gear => l1 = l2)
}


// All landing gears in the same state
fact SameStateGears {
	// always (all l1, l2 : Landing_Set | l1.landing_gear.stateG = l2.landing_gear.stateG)
}

// All doors in the same state
fact SameStateDoors {
	// always (all l1, l2 : Landing_Set | l1.door.stateD = l2.door.stateD)
}

// All electro valves are different
fact DifferentEV {
    // Landing_Set.close_EV != Landing_Set.open_EV
    // Landing_Set.close_EV != Landing_Set.retract_EV
    // Landing_Set.close_EV != Landing_Set.extend_EV
    // Landing_Set.open_EV != Landing_Set.retract_EV
    // Landing_Set.open_EV != Landing_Set.extend_EV
    // Landing_Set.retract_EV != Landing_Set.extend_EV
}

fact events {
    always (
        stutter or
        all d : Door | open_door [d] or
        all d : Door | close_door [d] or
        all l : Landing_Set | extend_gear [l] or
        all l : Landing_Set | retract_gear [l]
    )
}

pred open_door [d : Door] {
    // guards
    d.stateD = Closed

    // effects
    d.stateD' = Open

    // frame conditions
    all do : Door - d | do.stateD' = do.stateD
    stateG' = stateG
}

pred close_door [d : Door] {
    // guards
    d.stateD = Open

    // effects
    d.stateD' = Closed

    // frame conditions
    all do : Door - d | do.stateD' = do.stateD
    stateG' = stateG
}

pred extend_gear [l : Landing_Set] {
    // guards
    l.door.stateD = Open
    l.landing_gear.stateG = Retracted

    // effects
    l.landing_gear.stateG' = Extended

    // frame conditions
    all la : Landing_Gear - l.landing_gear | la.stateG' = la.stateG
    stateD' = stateD
}

pred retract_gear [l : Landing_Set] {
    // guards
    l.door.stateD = Open
    l.landing_gear.stateG = Extended

    // effects
    l.landing_gear.stateG' = Retracted

    // frame conditions
    all la : Landing_Gear - l.landing_gear | la.stateG' = la.stateG
    stateD' = stateD
}

pred stutter {
    stateD' = stateD
    stateG' = stateG
    position' = position
}

fact init {
    Door.stateD = Closed
    Landing_Gear.stateG = Retracted
    Pilot_Handle.position = Up
    Electro_Valve.stateE = Unstimulated
}

run Exemplo {
    Door.stateD = Closed
    eventually Landing_Gear.stateG = Extended
    
    // all l : Landing_Set | landing_seq[l]
}