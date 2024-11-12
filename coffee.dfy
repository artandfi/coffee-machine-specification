datatype Volume = Small | Medium | Large

function VolumeInMl(volume: Volume): real {
    match volume
        case Small => 100.0
        case Medium => 200.0
        case Large => 300.0
}

class CoffeeMachine {
    const blackCoffeeProportion: real := 0.05
    const espressoProportion: real := 0.5
    const cappuccinoProportion: real := 1.0 / 3.0
    const latteCoffeeProportion: real := 0.25
    const latteMilkProportion: real := 0.75
    const max_dispensed_sugar: nat := 4

    const max_coffee: real
    const max_water: real
    const max_milk: real
    const max_sugar: nat

    var coffee: real
    var water: real
    var milk: real
    var sugar: nat
    var on: bool
    var is_water_heated_up: bool
    var is_milk_heated_up: bool

    constructor(max_coffee: real, coffee: real, max_water: real, water: real, max_milk: real, milk: real, max_sugar: nat, sugar: nat)
        requires 0.0 <= coffee <= max_coffee
        requires 0.0 <= water <= max_water
        requires 0.0 <= milk <= max_milk
        requires 0 <= sugar <= max_sugar
        ensures this.max_coffee == max_coffee
        ensures this.max_water == max_water
        ensures this.max_milk == max_milk
        ensures this.max_sugar == max_sugar
        ensures this.coffee == coffee
        ensures this.water == water
        ensures this.milk == milk
        ensures this.sugar == sugar
        ensures !this.on
        ensures !this.is_water_heated_up
        ensures !this.is_milk_heated_up
    {
        this.max_coffee := max_coffee;
        this.max_water := max_water;
        this.max_milk := max_milk;
        this.max_sugar := max_sugar;

        this.coffee := coffee;
        this.water := water;
        this.milk := milk;
        this.sugar := sugar;

        this.on := false;
        this.is_water_heated_up := false;
        this.is_milk_heated_up := false;
    }

    method TurnOn()
        modifies this
        requires !this.on
        ensures this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.is_water_heated_up == old(this.is_water_heated_up)
        ensures this.is_milk_heated_up == old(this.is_milk_heated_up)
    {
        this.on := true;
    }

    method TurnOff()
        modifies this
        requires this.on
        ensures !this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.is_water_heated_up == old(this.is_water_heated_up)
        ensures this.is_milk_heated_up == old(this.is_milk_heated_up)
    {
        this.on := false;
    }

    method MakeBlackCoffee(volume: real, sugar: nat)
        modifies this
        requires this.on
        requires 0.0 <= volume <= this.water
        requires sugar <= this.sugar
        requires sugar <= this.max_dispensed_sugar
        requires this.coffee >= volume * this.blackCoffeeProportion
        ensures this.on
        ensures !this.is_water_heated_up
        ensures this.is_milk_heated_up == old(this.is_milk_heated_up)
        ensures this.coffee == old(this.coffee) - volume * this.blackCoffeeProportion
        ensures this.water == old(this.water) - volume
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar) - sugar
    {
        DispenseCoffee(volume * this.blackCoffeeProportion);
        HeatUpWater();
        PourWater(volume);
        DispenseSugar(sugar);
        CoolDownWater();
        
        print "Made black coffee";
    }

    method MakeEspresso(volume: real, sugar: nat)
        modifies this
        requires this.on
        requires 0.0 <= volume <= this.water
        requires sugar <= this.sugar
        requires sugar <= this.max_dispensed_sugar
        requires this.coffee >= volume * this.espressoProportion
        ensures this.on
        ensures !this.is_water_heated_up
        ensures this.is_milk_heated_up == old(this.is_milk_heated_up)
        ensures this.coffee == old(this.coffee) - volume * this.espressoProportion
        ensures this.water == old(this.water) - volume
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar) - sugar
    {
        DispenseCoffee(volume * this.espressoProportion);
        HeatUpWater();
        PourWater(volume);
        DispenseSugar(sugar);
        CoolDownWater();

        print "Made espresso";
    }

    method MakeCappuccino(volume: real, sugar: nat)
        modifies this
        requires this.on
        requires volume >= 0.0
        requires volume * this.cappuccinoProportion <= this.water
        requires sugar <= this.sugar
        requires sugar <= this.max_dispensed_sugar
        requires this.coffee >= volume * this.cappuccinoProportion * this.espressoProportion
        requires this.milk >= 2.0 * volume * this.cappuccinoProportion
        ensures this.on
        ensures !this.is_milk_heated_up
        ensures !this.is_water_heated_up
        ensures this.coffee == old(this.coffee) - volume * this.cappuccinoProportion * this.espressoProportion
        ensures this.water == old(this.water) - volume * this.cappuccinoProportion
        ensures this.milk == old(this.milk) - 2.0 * volume * this.cappuccinoProportion
        ensures this.sugar == old(this.sugar) - sugar
    {
        MakeEspresso(volume * this.cappuccinoProportion, 0);
        HeatUpMilk();
        PourMilk(volume * this.cappuccinoProportion);
        SteamMilk(volume * this.cappuccinoProportion);
        DispenseSugar(sugar);
        CoolDownMilk();

        print "Made cappuccino";
    }

    method MakeLatte(volume: real, sugar: nat)
        modifies this
        requires this.on
        requires volume >= 0.0
        requires volume * this.latteCoffeeProportion <= this.water
        requires sugar <= this.sugar
        requires sugar <= this.max_dispensed_sugar
        requires this.coffee >= volume * this.latteCoffeeProportion * this.espressoProportion
        requires this.milk >= volume * this.latteMilkProportion
        ensures this.on
        ensures !this.is_milk_heated_up
        ensures !this.is_water_heated_up
        ensures this.coffee == old(this.coffee) - volume * this.latteCoffeeProportion * this.espressoProportion
        ensures this.water == old(this.water) - volume * this.latteCoffeeProportion
        ensures this.milk == old(this.milk) - volume * this.latteMilkProportion
        ensures this.sugar == old(this.sugar) - sugar
    {
        MakeEspresso(volume * this.latteCoffeeProportion, 0);
        HeatUpMilk();
        SteamMilk(volume * this.latteMilkProportion);
        DispenseSugar(sugar);
        CoolDownMilk();

        print "Made latte";
    }

    method DispenseCoffee(mass: real)
        modifies this
        requires this.on
        requires 0.0 <= mass <= this.coffee
        ensures this.on
        ensures this.coffee == old(this.coffee) - mass
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.is_water_heated_up == old(is_water_heated_up)
    {
        this.coffee := this.coffee - mass;
        print "Dispensed the coffee";
    }

    method DispenseSugar(number: nat)
        modifies this
        requires this.on
        requires number <= this.sugar
        ensures this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar) - number
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.is_water_heated_up == old(is_water_heated_up)
    {
        this.sugar := this.sugar - number;
        print "Dispensed the sugar";
    }

    method PourWater(volume: real)
        modifies this
        requires this.on
        requires this.is_water_heated_up
        requires 0.0 <= volume <= this.water
        ensures this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water) - volume
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.is_water_heated_up == old(is_water_heated_up)
    {
        this.water := this.water - volume;
        print "Poured the water";
    }

    method PourMilk(volume: real)
        modifies this
        requires this.on
        requires this.is_milk_heated_up
        requires 0.0 <= volume <= this.milk
        ensures this.on
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk) - volume
        ensures this.sugar == old(this.sugar)
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.is_water_heated_up == old(is_water_heated_up)
    {
        this.milk := this.milk - volume;
        print "Poured the milk";
    }
    
    method SteamMilk(volume: real)
        modifies this
        requires this.on
        requires this.is_milk_heated_up
        requires 0.0 <= volume <= this.milk
        ensures this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk) - volume
        ensures this.sugar == old(this.sugar)
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.is_water_heated_up == old(is_water_heated_up)
    {
        this.milk := this.milk - volume;
        print "Steamed the milk";
    }

    method RefillCoffee(mass: real)
        modifies this
        requires !this.on
        requires mass >= 0.0
        requires this.coffee + mass <= this.max_coffee
        ensures !this.on
        ensures this.coffee == old(this.coffee) + mass
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.is_water_heated_up == old(is_water_heated_up)
    {
        this.coffee := this.coffee + mass;
    }

    method RefillWater(volume: real)
        modifies this
        requires !this.on
        requires volume >= 0.0
        requires this.water + volume <= this.max_water
        ensures !this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water) + volume
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.is_water_heated_up == old(is_water_heated_up)
    {
        this.water := this.water + volume;
    }

    method RefillMilk(volume: real)
        modifies this
        requires !this.on
        requires volume >= 0.0
        requires this.milk + volume <= this.max_milk
        ensures !this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk) + volume
        ensures this.sugar == old(this.sugar)
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.is_water_heated_up == old(is_water_heated_up)
    {
        this.milk := this.milk + volume;
    }
    
    method RefillSugar(number: nat)
        modifies this
        requires !this.on
        requires this.sugar + number <= this.max_sugar
        ensures !this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar) + number
        ensures this.is_milk_heated_up == old(is_milk_heated_up)
        ensures this.is_water_heated_up == old(is_water_heated_up)
    {
        this.sugar := this.sugar + number;
    }

    method HeatUpWater()
        modifies this
        requires this.on
        ensures this.on
        ensures this.is_water_heated_up
        ensures this.is_milk_heated_up == old(this.is_milk_heated_up)
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
    {
        this.is_water_heated_up := true;
        print "Heated up the water";
    }

    method HeatUpMilk()
        modifies this
        requires this.on
        ensures this.on
        ensures this.is_water_heated_up == old(is_water_heated_up)
        ensures this.is_milk_heated_up
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
    {
        this.is_milk_heated_up := true;
        print "Heated up the milk";
    }

    method CoolDownWater()
        modifies this
        requires this.on
        requires this.is_water_heated_up
        ensures this.on
        ensures !this.is_water_heated_up
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.is_milk_heated_up == old(this.is_milk_heated_up)
    {
        this.is_water_heated_up := false;
    }

    method CoolDownMilk()
        modifies this
        requires this.on
        requires this.is_milk_heated_up
        ensures this.on
        ensures !this.is_milk_heated_up
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.is_water_heated_up == old(this.is_water_heated_up)
    {
        this.is_milk_heated_up := false;
    }
}
