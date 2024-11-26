class Volume {
    static const small: real := 100.0
    static const medium: real := 200.0
    static const large: real := 300.0
}

class CoffeeMachine {
    const blackCoffeeProportion: real := 0.05
    const blackCoffeeWaterProportion: real := 0.95
    const espressoCoffeeProportion: real := 1.0 / 3.0
    const espressoWaterProportion: real := 2.0 / 3.0
    const cappuccinoProportion: real := 1.0 / 3.0
    const latteCoffeeProportion: real := 0.25
    const latteMilkProportion: real := 0.75
    const maxDispensedSugar: nat := 4

    const maxCoffee: real
    const maxWater: real
    const maxMilk: real
    const maxSugar: nat

    var coffee: real
    var water: real
    var milk: real
    var sugar: nat
    var on: bool
    var isWaterHeatedUp: bool
    var isMilkHeatedUp: bool

    constructor(maxCoffee: real, coffee: real, maxWater: real, water: real, maxMilk: real, milk: real, maxSugar: nat, sugar: nat)
        requires 0.0 <= coffee <= maxCoffee
        requires 0.0 <= water <= maxWater
        requires 0.0 <= milk <= maxMilk
        requires 0 <= sugar <= maxSugar
        ensures this.maxCoffee == maxCoffee
        ensures this.maxWater == maxWater
        ensures this.maxMilk == maxMilk
        ensures this.maxSugar == maxSugar
        ensures this.coffee == coffee
        ensures this.water == water
        ensures this.milk == milk
        ensures this.sugar == sugar
        ensures !this.on
        ensures !this.isWaterHeatedUp
        ensures !this.isMilkHeatedUp
    {
        this.maxCoffee := maxCoffee;
        this.maxWater := maxWater;
        this.maxMilk := maxMilk;
        this.maxSugar := maxSugar;

        this.coffee := coffee;
        this.water := water;
        this.milk := milk;
        this.sugar := sugar;

        this.on := false;
        this.isWaterHeatedUp := false;
        this.isMilkHeatedUp := false;
    }

    method TurnOn()
        modifies this
        requires !this.on
        ensures this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.isWaterHeatedUp == old(this.isWaterHeatedUp)
        ensures this.isMilkHeatedUp == old(this.isMilkHeatedUp)
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
        ensures this.isWaterHeatedUp == old(this.isWaterHeatedUp)
        ensures this.isMilkHeatedUp == old(this.isMilkHeatedUp)
    {
        this.on := false;
    }

    method MakeBlackCoffee(volume: real, sugar: nat)
        modifies this
        requires this.on
        requires 0.0 <= volume * this.blackCoffeeWaterProportion <= this.water
        requires sugar <= this.sugar
        requires sugar <= this.maxDispensedSugar
        requires this.coffee >= volume * this.blackCoffeeProportion
        ensures this.on
        ensures !this.isWaterHeatedUp
        ensures this.isMilkHeatedUp == old(this.isMilkHeatedUp)
        ensures this.coffee == old(this.coffee) - volume * this.blackCoffeeProportion
        ensures this.water == old(this.water) - volume * this.blackCoffeeWaterProportion
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar) - sugar
    {
        DispenseCoffee(volume * this.blackCoffeeProportion);
        HeatUpWater();
        PourWater(volume * this.blackCoffeeWaterProportion);
        DispenseSugar(sugar);
        CoolDownWater();
        
        print "Made black coffee";
    }

    method MakeEspresso(volume: real, sugar: nat)
        modifies this
        requires this.on
        requires 0.0 <= volume * this.espressoWaterProportion <= this.water
        requires sugar <= this.sugar
        requires sugar <= this.maxDispensedSugar
        requires this.coffee >= volume * this.espressoCoffeeProportion
        ensures this.on
        ensures !this.isWaterHeatedUp
        ensures this.isMilkHeatedUp == old(this.isMilkHeatedUp)
        ensures this.coffee == old(this.coffee) - volume * this.espressoCoffeeProportion
        ensures this.water == old(this.water) - volume * this.espressoWaterProportion
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar) - sugar
    {
        DispenseCoffee(volume * this.espressoCoffeeProportion);
        HeatUpWater();
        PourWater(volume * this.espressoWaterProportion);
        DispenseSugar(sugar);
        CoolDownWater();

        print "Made espresso";
    }

    method MakeCappuccino(volume: real, sugar: nat)
        modifies this
        requires this.on
        requires volume >= 0.0
        requires this.water >= volume * this.cappuccinoProportion * this.espressoWaterProportion
        requires this.coffee >= volume * this.cappuccinoProportion * this.espressoCoffeeProportion
        requires this.milk >= 2.0 * volume * this.cappuccinoProportion
        requires sugar <= this.sugar
        requires sugar <= this.maxDispensedSugar
        ensures this.on
        ensures !this.isMilkHeatedUp
        ensures !this.isWaterHeatedUp
        ensures this.coffee == old(this.coffee) - volume * this.cappuccinoProportion * this.espressoCoffeeProportion
        ensures this.water == old(this.water) - volume * this.cappuccinoProportion * this.espressoWaterProportion
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
        requires this.water >= volume * this.latteCoffeeProportion * this.espressoWaterProportion
        requires this.coffee >= volume * this.latteCoffeeProportion * this.espressoCoffeeProportion
        requires this.milk >= volume * this.latteMilkProportion
        requires sugar <= this.sugar
        requires sugar <= this.maxDispensedSugar
        ensures this.on
        ensures !this.isMilkHeatedUp
        ensures !this.isWaterHeatedUp
        ensures this.coffee == old(this.coffee) - volume * this.latteCoffeeProportion * this.espressoCoffeeProportion
        ensures this.water == old(this.water) - volume * this.latteCoffeeProportion * this.espressoWaterProportion
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
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
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
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
    {
        this.sugar := this.sugar - number;
        print "Dispensed the sugar";
    }

    method PourWater(volume: real)
        modifies this
        requires this.on
        requires this.isWaterHeatedUp
        requires 0.0 <= volume <= this.water
        ensures this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water) - volume
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
    {
        this.water := this.water - volume;
        print "Poured the water";
    }

    method PourMilk(volume: real)
        modifies this
        requires this.on
        requires this.isMilkHeatedUp
        requires 0.0 <= volume <= this.milk
        ensures this.on
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk) - volume
        ensures this.sugar == old(this.sugar)
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
    {
        this.milk := this.milk - volume;
        print "Poured the milk";
    }
    
    method SteamMilk(volume: real)
        modifies this
        requires this.on
        requires this.isMilkHeatedUp
        requires 0.0 <= volume <= this.milk
        ensures this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk) - volume
        ensures this.sugar == old(this.sugar)
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
    {
        this.milk := this.milk - volume;
        print "Steamed the milk";
    }

    method RefillCoffee(mass: real)
        modifies this
        requires !this.on
        requires mass >= 0.0
        requires this.coffee + mass <= this.maxCoffee
        ensures !this.on
        ensures this.coffee == old(this.coffee) + mass
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
    {
        this.coffee := this.coffee + mass;
    }

    method RefillWater(volume: real)
        modifies this
        requires !this.on
        requires volume >= 0.0
        requires this.water + volume <= this.maxWater
        ensures !this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water) + volume
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
    {
        this.water := this.water + volume;
    }

    method RefillMilk(volume: real)
        modifies this
        requires !this.on
        requires volume >= 0.0
        requires this.milk + volume <= this.maxMilk
        ensures !this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk) + volume
        ensures this.sugar == old(this.sugar)
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
    {
        this.milk := this.milk + volume;
    }
    
    method RefillSugar(number: nat)
        modifies this
        requires !this.on
        requires this.sugar + number <= this.maxSugar
        ensures !this.on
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar) + number
        ensures this.isMilkHeatedUp == old(isMilkHeatedUp)
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
    {
        this.sugar := this.sugar + number;
    }

    method HeatUpWater()
        modifies this
        requires this.on
        ensures this.on
        ensures this.isWaterHeatedUp
        ensures this.isMilkHeatedUp == old(this.isMilkHeatedUp)
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
    {
        this.isWaterHeatedUp := true;
        print "Heated up the water";
    }

    method HeatUpMilk()
        modifies this
        requires this.on
        ensures this.on
        ensures this.isWaterHeatedUp == old(isWaterHeatedUp)
        ensures this.isMilkHeatedUp
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
    {
        this.isMilkHeatedUp := true;
        print "Heated up the milk";
    }

    method CoolDownWater()
        modifies this
        requires this.on
        requires this.isWaterHeatedUp
        ensures this.on
        ensures !this.isWaterHeatedUp
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.isMilkHeatedUp == old(this.isMilkHeatedUp)
    {
        this.isWaterHeatedUp := false;
    }

    method CoolDownMilk()
        modifies this
        requires this.on
        requires this.isMilkHeatedUp
        ensures this.on
        ensures !this.isMilkHeatedUp
        ensures this.coffee == old(this.coffee)
        ensures this.water == old(this.water)
        ensures this.milk == old(this.milk)
        ensures this.sugar == old(this.sugar)
        ensures this.isWaterHeatedUp == old(this.isWaterHeatedUp)
    {
        this.isMilkHeatedUp := false;
    }
}

method Main() {
    var coffee := 1000.0;
    var water := 1000.0;
    var milk := 1000.0;
    var sugar := 100;
    var coffeeMachine := new CoffeeMachine(coffee, coffee, water, water, milk, milk, sugar, sugar);

    coffeeMachine.TurnOn();

    coffeeMachine.MakeBlackCoffee(Volume.small, 2);
    coffeeMachine.MakeLatte(Volume.large, 3);
    coffeeMachine.MakeEspresso(Volume.medium, 4);
    coffeeMachine.MakeCappuccino(Volume.small, 1);
    coffeeMachine.MakeLatte(Volume.medium, 0);
    coffeeMachine.MakeLatte(Volume.large, 4);
    coffeeMachine.MakeLatte(Volume.large, 4);
    // coffeeMachine.MakeLatte(Volume.large, 4); not enough
}