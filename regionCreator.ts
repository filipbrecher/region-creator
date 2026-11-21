// state shared by the packability check
type RegionCreatorPacking = {
    fieldSizes: number[];       // free cells left in each field
    sizesToPack: number[];      // sizes of the regions that still have to fit
    necessaryFields: number[];  // fields that must be filled exactly
    optionalFields: number[];   // fields that may keep space left over
};

// fields a region fits in, grouped by field size: fields[i] all have sizes[i] free cells
type RegionCreatorFieldGroups = {
    sizes: number[];
    fields: number[][];
    space: number;  // how many regions of the checked size fit into all of the fields together
};

type RegionCreatorMode =
    "default" |   // randomly choose the next cell of a region from all possible neighbors
    "spaghetti" | // minimize cell neighbors from the same regions
    "blob";       // generate circle/clump-like regions

class RegionCreator {

    public doLog: boolean = false;
    public maxOneTime: number = 1;
    public maxTime: number = 10;
    public maxTries: number = 100;
    public maxRegionSizeTries: number = 10000; // how many times createNewRegionSizes may retry before giving up
    public generateFaster: boolean = true; // if true, generates the first cell of each region in the spot starting from the smallest ids,
                                     // if false, generates the first cell in a random free spot
    public mode: RegionCreatorMode = "default";

    private readonly masterWidth: number | null = null;
    private readonly givenPairs: [number, number][] | null = null;
    private readonly originalCellIds: number[]; // id encoding
    private cellCount: number;

    // each cell is numbered from 0 to size-1
    private baseNeighbors: number[][];  // at nth position are the nth cell's neighbors
    private baseFieldForCell: number[];  // at nth position is the field number the cell n is in
    private baseCellsForFields: number[][];  // at kth position are stored the cells' numbers that are in the kth field
    private _hasBoard: boolean = false;
    public get hasBoard(): boolean {
        return this._hasBoard;
    }
    private _board: number[] = [];
    public get board(): number[] {
        return RegionCreatorUtils.arrayDeepcopy(this._board);
    }
    private _regions: number[][] = [];
    public get regions(): number[][] {
        return RegionCreatorUtils.arrayDeepcopy(this._regions);
    }

    // region sizes and shapes
    private _forcedRegionSizes: number[] = [];  // region sizes that must be present
    public set forcedRegionSizes(sizes: number[] | null) {
        this._forcedRegionSizes = sizes === null ? [] : RegionCreatorUtils.arrayDeepcopy(sizes);
    }
    private baseRegionSizes: number[] = [1];
    public get regionSizes(): number[] {  // the sizes created by createNewRegionSizes
        return RegionCreatorUtils.arrayDeepcopy(this.baseRegionSizes);
    }
    private baseRegionCount: number = 1;

    // region conditions
    private strictness: number = 0;  // how much do the random sizes not deviate from width and/or height - 0(max) to 1(min deviation)
    private smallerRegionChance: number = 0.5;  // desired percentage of regionCreator smaller than the avgRegionSize, must be between 0 and 1
    private includeAvgRegionSize: boolean = true;  // if false, then avgRegionSize must not be equal to min and max RegionSize
    private avgRegionSize: number = 1;  // must be integer between 1 and (cellCount - sum of baseRegionSizes) (including) and must be between min and max RegionSize
    private minRegionSize: number = 1;  // must be integer between 1 and (cellCount - sum of baseRegionSizes) (including) and must be smaller or equal to maxRegionSize
    private maxRegionSize: number = 1;  // must be integer between 1 and (cellCount - sum of baseRegionSizes) (including) and must be bigger or equal to minRegionSize

    private then: number = new Date().getTime();
    private thenOne: number = new Date().getTime();
    // variables to help with the generation
    private regionSizesLeft: number[] = [];  // sizes of the regions that still need to be placed
    private regionCount: number = 1;
    private freeNeighbors: number[][] = [[]];
    private regionForCell: number[] = [];
    private fieldForCell: number[] = [];
    private cellsForFields: number[][] = [[]];
    private neighboringCells: number[] = [];
    private neighboringFields: number[] = [];
    private neighborsToExclude: number[] = [];  // save neighbor cells which weren't possible for parenthetical cells bcs they aren't possible even for the children's

    // input - the numbers in neighborPairs must be given in the range of originalCellIds or cellCount, otherwise they won't be taken in account
    //         cellCount: number (starting from 0), masterWidth: number ||
    //         originalCellIds: number[], masterWidth: number ||
    //         originalCellIds: number[], neighborPairs: [number, number][]
    //         cellCount: number (starting from 0), neighborPairs: [number, number][]
    constructor(cellIdentifier: number[] | number, pairIdentifier: number | [number, number][]) {
        if (typeof cellIdentifier === "number") {
            if (cellIdentifier < 1) {
                throw new RangeError("RegionCreator: cellCount (cellIdentifier) can't be smaller than 1.");
            }
            this.originalCellIds = RegionCreatorUtils.createArrayIncremented(0, cellIdentifier);
            this.cellCount = this.originalCellIds.length;
        } else {
            this.originalCellIds = RegionCreatorUtils.arrayDeepcopy(cellIdentifier).sort((a: number, b: number) => { return a - b; });
            this.cellCount = this.originalCellIds.length;
        }
        if (typeof pairIdentifier === "number") {
            if (pairIdentifier < 1) {
                throw new RangeError("RegionCreator: masterWidth (pairIdentifier) can't be smaller than 1.");
            }
            this.masterWidth = pairIdentifier;
        } else {
            this.givenPairs = RegionCreatorUtils.arrayDeepcopy(pairIdentifier);
        }

        if (this.masterWidth !== null) {
            this.baseNeighbors = RegionCreator.getBaseNeighborsByWidth(this.originalCellIds, this.masterWidth);
        } else {
            this.baseNeighbors = RegionCreator.getBaseNeighborsByPairs(this.originalCellIds, this.givenPairs!);
        }

        [this.baseFieldForCell, this.baseCellsForFields] = RegionCreator.getBaseFields(this.baseNeighbors);
    }

    private static getBaseFields(baseNeighbors: number[][]): [number[], number[][]] {
        let cellCount = baseNeighbors.length;
        let leftCells = RegionCreatorUtils.createArrayIncremented(0, cellCount);

        let baseFieldForCell = RegionCreatorUtils.createArray1d(cellCount, -1);
        let baseCellsForFields = [];

        let nextField: number[];
        let cellsToCheck: number[];
        let cellId: number;
        let neighborId: number;
        while (leftCells.length > 0) {
            nextField = [];
            cellsToCheck = [leftCells.pop()!];
            while (cellsToCheck.length > 0) {
                cellId = cellsToCheck.pop()!;
                leftCells = RegionCreatorUtils.arrayRemoveOne(leftCells, cellId);
                nextField.push(cellId);
                for (let i = 0; i < baseNeighbors[cellId].length; i++) {
                    neighborId = baseNeighbors[cellId][i];
                    if (nextField.indexOf(neighborId) === -1 && cellsToCheck.indexOf(neighborId) === -1) {
                        cellsToCheck.push(neighborId);
                    }
                }
            }

            for (let i = 0; i < nextField.length; i++) {
                baseFieldForCell[nextField[i]] = baseCellsForFields.length;
            }
            baseCellsForFields.push(nextField);
        }

        return [baseFieldForCell, baseCellsForFields];
    }

    private static getBaseNeighborsByPairs(originalCellIds: number[], pairs: [number, number][]): number[][] {
        let neighbors: number[][] = [];
        for (let i = 0; i < originalCellIds.length; i++) {
            neighbors.push([]);
        }

        for (let i = 0; i < pairs.length; i++) {
            let newIdFirst = originalCellIds.indexOf(pairs[i][0]);
            let newIdSecond = originalCellIds.indexOf(pairs[i][1]);
            if (newIdFirst === -1 || newIdSecond === -1 || newIdFirst === newIdSecond) {
                continue;
            }

            if (neighbors[newIdFirst].indexOf(newIdSecond) === -1) {
                neighbors[newIdFirst].push(newIdSecond);
                neighbors[newIdSecond].push(newIdFirst);
            }
        }

        return neighbors;
    }

    private static getBaseNeighborsByWidth(originalCellIds: number[], masterWidth: number): number[][] {
        // originalCellIds must be sorted and there must be no duplicates
        let spacings = [1, masterWidth]; // right, down
        let neighbors: number[][] = [];
        for (let i = 0; i < originalCellIds.length; i++) {
            neighbors.push([]);
        }

        for (let i = 0; i < originalCellIds.length; i++) {
            let originalIndex = originalCellIds[i];
            for (let j = 0; j < 2; j++) { // for each half-direction
                if (j === 0 && (originalIndex % masterWidth === masterWidth - 1 || originalIndex % masterWidth === -1)) {
                    continue;
                }
                for (let k = i + 1; k <= i + spacings[j]; k++) {
                    if (k < 0 || k >= originalCellIds.length) {
                        break;
                    }
                    if (originalCellIds[k] - originalCellIds[i] === spacings[j]) {
                        neighbors[i].push(k);
                        neighbors[k].push(i);
                        break;
                    }
                }
            }
        }
        return neighbors;
    }

    // REGION SIZES AND SHAPES

    public setRegionConditions(
        strictness: number|null = null,
        smallerRegionChance: number|null = null,
        includeAvgRegionSize: boolean|null = null,
        avgRegionSize: number|null = null,
        minRegionSize: number|null = null,
        maxRegionSize: number|null = null
    ): void {
        this.strictness = strictness === null ? 0 : strictness;
        this.smallerRegionChance = smallerRegionChance === null ? 0.2 : smallerRegionChance;
        this.includeAvgRegionSize = includeAvgRegionSize === null ? true : includeAvgRegionSize;
        this.avgRegionSize = avgRegionSize === null ? Math.floor((this.cellCount)**(1/2)) : avgRegionSize;
        this.minRegionSize = avgRegionSize === null ? 1 : avgRegionSize;  // if minRS is null, then if avgRS is set, it is the same
        this.minRegionSize = minRegionSize === null ? this.minRegionSize : minRegionSize;
        this.maxRegionSize = avgRegionSize === null ? this.cellCount : avgRegionSize;  // if maxRS is null, then if avgRS is set, it is the same
        this.maxRegionSize = maxRegionSize === null ? this.maxRegionSize : maxRegionSize;
        if (this.strictness < 0) {
            this.strictness = 0;
        } else if (this.strictness > 1) {
            this.strictness = 1;
        }
        if (this.minRegionSize < 1) {
            this.minRegionSize = 1;
        } else if (this.minRegionSize > this.cellCount) {
            this.minRegionSize = this.cellCount;
        }
        if (this.maxRegionSize < this.minRegionSize) {
            this.maxRegionSize = this.minRegionSize;
        } else if (this.maxRegionSize > this.cellCount) {
            this.maxRegionSize = this.cellCount;
        }
        if (this.avgRegionSize < this.minRegionSize || this.avgRegionSize > this.maxRegionSize) {
            this.avgRegionSize = Math.floor((this.minRegionSize + this.maxRegionSize)/2);
        }
        if ( !this.includeAvgRegionSize && (this.minRegionSize === this.avgRegionSize || this.maxRegionSize === this.avgRegionSize)) {
            throw new RangeError("RegionCreator: if includeAvgRegionSize is false, minRegionSize and maxRegionSize can't equal avgRegionSize.");
        }
        return;
    }

    private setBaseRegionSizes(): void {
        for (const size of this._forcedRegionSizes) {
            if ( !Number.isInteger(size) || size < 1) {
                throw new RangeError(`RegionCreator: forced region sizes must be integers bigger than 0, got ${size}.`);
            }
        }
        if (RegionCreatorUtils.arrayGetSum(this._forcedRegionSizes) > this.cellCount) {
            throw new RangeError("RegionCreator: the forced region sizes add up to more than the cell count.");
        }

        let tryAgain = true;
        let tries = 0;
        while (tryAgain) {
            if (tries >= this.maxRegionSizeTries) {
                throw new Error(`RegionCreator: couldn't generate region sizes in ${this.maxRegionSizeTries} tries, the region conditions may be impossible to meet.`);
            }
            tries += 1;
            tryAgain = false;
            this.baseRegionSizes = RegionCreatorUtils.arrayDeepcopy(this._forcedRegionSizes);
            let sizeLeft = this.cellCount - RegionCreatorUtils.arrayGetSum(this.baseRegionSizes);
            while (sizeLeft > 0 && !tryAgain) {
                let isSmaller = Math.random() < this.smallerRegionChance;
                let leeway = isSmaller ? this.avgRegionSize - this.minRegionSize + 1 : this.maxRegionSize - this.avgRegionSize + 1;
                if (!this.includeAvgRegionSize) {
                    leeway -= 1;
                }
                let relativeDeviation = Math.random();
                if (this.strictness < 1) {
                    relativeDeviation **= 1 / (1 - this.strictness);
                } else {
                    relativeDeviation = 0;
                }
                let deviation = Math.floor(relativeDeviation * leeway);
                if (!this.includeAvgRegionSize) {
                    deviation += 1;
                }
                deviation = isSmaller ? -1 * deviation : deviation;
                let newSize = this.avgRegionSize + deviation;
                if (newSize > sizeLeft) {  // make a better way to deal with it, bcs then a region of not very possible sizes bcs of strictness
                    newSize = sizeLeft;
                    if (newSize < this.minRegionSize || (newSize === this.avgRegionSize && !this.includeAvgRegionSize)) {
                        tryAgain = true;
                    }
                } else if (sizeLeft - newSize < this.minRegionSize && sizeLeft < this.maxRegionSize) {
                    newSize = sizeLeft;
                }
                sizeLeft -= newSize;
                this.baseRegionSizes.push(newSize);
            }
        }
        return;
    }

    public createNewRegionSizes(): void {
        this.setBaseRegionSizes();
        if (this.generateFaster) {
            RegionCreatorUtils.arrayShuffle(this.baseRegionSizes);
        } else {
            this.baseRegionSizes = RegionCreatorUtils.arraySortNumbers(this.baseRegionSizes, true);
        }
        this.baseRegionCount = this.baseRegionSizes.length;
        if (this.doLog) {
            console.log("RegionCreator - generated region sizes:", this.baseRegionSizes);
        }
        return;
    }

    // CREATE NEW BOARD

    public createNewBoard(): void {
        this.then = new Date().getTime();
        let tries = 0;

        this._board = RegionCreatorUtils.createArray1d(this.cellCount, -1);
        this._hasBoard = false;
        while ( !this._hasBoard) {
            this.thenOne = new Date().getTime();
            this.copyBaseValues();
            this.placeNextRegion();

            let now = new Date().getTime();
            if (((now - this.then) / 1000) >= this.maxTime) {
                break;
            }
            tries += 1;
            if (tries >= this.maxTries) {
                break;
            }
        }
        this._board = RegionCreatorUtils.arrayDeepcopy(this.regionForCell);
        this._regions = this.getRegionsFromBoard();

        if (this.doLog) {
            let now = new Date().getTime();
            console.log(`RegionCreator - ${(now - this.then) / 1000}s, ${tries} tries`);
        }
        return;
    }

    private copyBaseValues(): void {
        this.regionSizesLeft = RegionCreatorUtils.arrayDeepcopy(this.baseRegionSizes);
        this.regionCount = this.baseRegionCount;
        this.freeNeighbors = RegionCreatorUtils.arrayDeepcopy(this.baseNeighbors);
        this.regionForCell = RegionCreatorUtils.createArray1d(this.cellCount, -1);
        this.fieldForCell = RegionCreatorUtils.arrayDeepcopy(this.baseFieldForCell);
        this.cellsForFields = RegionCreatorUtils.arrayDeepcopy(this.baseCellsForFields);
    }

    private getRegionsFromBoard(): number[][] {
        let regions = [];
        for (let i = 0; i < this.regionCount; i++) {
            let region = [];
            for (let j = 0; j < this._board.length; j++) {
                if (this._board[j] === i) {
                    region.push(this.originalCellIds[j]);
                }
            }
            regions.push(region);
        }
        return regions;
    }

    // PLACE NEXT REGION

    private placeNextRegion(): void {
        if (this.regionSizesLeft.length === 0) {
            this._hasBoard = true;
            return;
        }

        let currRegionSize = this.regionSizesLeft.pop()!;
        let currRegionId = this.regionCount - this.regionSizesLeft.length - 1;
        this.neighboringFields = [];
        this.neighboringCells = [];
        this.neighborsToExclude = [];

        let cellsPlaced = this.tryPlaceNextCell(currRegionSize, currRegionId, currRegionSize);
        if (cellsPlaced) {
            this.placeNextRegion();
        }
        return;
    }

    // PLACE NEXT CELL

    private tryPlaceNextCell(regionSize: number, regionId: number, cellsLeftToPlace: number): boolean {
        if (cellsLeftToPlace === 0) {
            return true;
        }

        let now = new Date().getTime();
        if ((now - this.thenOne) / 1000 >= this.maxOneTime || (now - this.then) / 1000 >= this.maxTime) {
            return false;
        }

        let starterCells = this.getStarterCells(regionSize, regionId, cellsLeftToPlace);
        let neighborsExcluded = 0;

        for (let i = 0; i < starterCells.length; i++) {
            let cellId = starterCells[i];

            // place the cell
            let prevFieldId = this.placeCell(regionId, cellId);
            // add appropriate new neighbors
            let addedNeighbors = this.addNewNeighbors(regionSize, cellsLeftToPlace, prevFieldId, cellId);
            // separate fields that got divided
            let addedFields = this.separateFields(prevFieldId, cellId);

            // check packability
            let isPackable = this.checkPackability(regionSize, cellsLeftToPlace);
            // place next cell
            if (isPackable) {
                cellsLeftToPlace -= 1;
                let isPlaceable = this.tryPlaceNextCell(regionSize, regionId, cellsLeftToPlace);
                cellsLeftToPlace += 1;
                if (isPlaceable) {
                    return true;
                }
            }

            this.neighborsToExclude.push(cellId);
            neighborsExcluded += 1;
            // undo fields
            this.undoSeparateFields(addedFields, prevFieldId);
            // undo neighbors
            this.undoAddNewNeighbors(regionSize, cellsLeftToPlace, cellId, addedNeighbors, prevFieldId);
            // undo cell
            this.undoPlaceCell(cellId, prevFieldId);
        }
        this.neighborsToExclude.length -= neighborsExcluded;

        return false;
    }

    private getStarterCells(regionSize: number, regionId: number, cellsLeftToPlace: number): number[] {
        let starterCells = [];
        if (regionSize === cellsLeftToPlace) { // if this is the first cell, set an array of all possible first placements (from fields that are equal or bigger size)
            for (let i = 0; i < this.cellsForFields.length; i++) {
                let fieldSize = this.cellsForFields[i].length;
                if (fieldSize >= regionSize) {
                    for (let j = 0; j < fieldSize; j++) {
                        starterCells.push(this.cellsForFields[i][j]);
                    }
                }
            }
            if (this.generateFaster) {
                RegionCreatorUtils.arraySortNumbers(starterCells, true);
            } else {
                RegionCreatorUtils.arrayShuffle(starterCells)
            }
        } else {
            starterCells = [];
            for (let i = 0; i < this.neighboringCells.length; i++) {
                if (this.neighborsToExclude.indexOf(this.neighboringCells[i]) === -1) {
                    starterCells.push(this.neighboringCells[i]);
                }
            }
            if (this.mode === "blob") {
                if (Math.random() < 0.4) {
                    RegionCreatorUtils.arrayShuffle(starterCells);
                }
            } else {
                RegionCreatorUtils.arrayShuffle(starterCells);
            }
            if (this.mode === "spaghetti") {
                let neighborCounts = new Map<number, number>();  // how many neighbors of a starterCell are in the current region
                for (const cellId of starterCells) {
                    let neighborCount = 0;
                    for (const neighborId of this.baseNeighbors[cellId]) {
                        if (this.regionForCell[neighborId] === regionId) {
                            neighborCount += 1;
                        }
                    }
                    neighborCounts.set(cellId, neighborCount);
                }
                // stable sort: cells with fewer neighbors in the region first, shuffled order kept within equal counts
                starterCells.sort((a, b) => neighborCounts.get(a)! - neighborCounts.get(b)!);
            }
        }
        return starterCells;
    }

    private placeCell(regionId: number, cellId: number): number {
        this.regionForCell[cellId] = regionId;
        let prevFieldId = this.fieldForCell[cellId];
        this.fieldForCell[cellId] = -1;
        let cellNeighbors = this.freeNeighbors[cellId];
        for (let i = 0; i < cellNeighbors.length; i++) {
            this.freeNeighbors[cellNeighbors[i]] = RegionCreatorUtils.arrayRemoveOne(this.freeNeighbors[cellNeighbors[i]], cellId);
        }
        this.cellsForFields[prevFieldId] = RegionCreatorUtils.arrayRemoveOne(this.cellsForFields[prevFieldId], cellId);
        return prevFieldId;
    }

    private addNewNeighbors(regionSize: number, cellsLeftToPlace: number, prevFieldId: number, cellId: number): number[] {
        if (regionSize !== cellsLeftToPlace) {
            this.neighboringCells = RegionCreatorUtils.arrayRemoveOne(this.neighboringCells, cellId);
        } else {
            this.neighboringFields.push(prevFieldId)
        }
        let addedNeighbors = [];
        let cellNeighbors = this.freeNeighbors[cellId];
        for (let i = 0; i < cellNeighbors.length; i++) {
            let cellNeighbor = cellNeighbors[i];
            if (this.neighboringCells.indexOf(cellNeighbor) === -1) {
                addedNeighbors.push(cellNeighbor);
                this.neighboringCells.push(cellNeighbor);
            }
        }
        return addedNeighbors;
    }

    private separateFields(prevFieldId: number, cellId: number): number[] {
        let addedFields: number[];
        addedFields = [];
        if (this.freeNeighbors[cellId].length > 1) {
            let neighborsForFields = this.getFieldsForCells(cellId);
            if (neighborsForFields.length > 1) {
                for (let i = 1; i < neighborsForFields.length; i++) {
                    let fieldId = this.cellsForFields.length;
                    addedFields.push(fieldId);
                    this.neighboringFields.push(fieldId);
                    let addedFieldCells: number[];
                    addedFieldCells = [];
                    let neighborsForField = neighborsForFields[i];
                    for (let j = 0; j < neighborsForField.length; j++) {
                        let neighbor = neighborsForField[j];
                        this.fieldForCell[neighbor] = fieldId;
                        this.cellsForFields[prevFieldId] = RegionCreatorUtils.arrayRemoveOne(this.cellsForFields[prevFieldId], neighbor);
                        addedFieldCells.push(neighbor);
                    }
                    this.cellsForFields.push(addedFieldCells);
                }
            }
        }

        return addedFields;
    }

    private getFieldsForCells(cellId: number): number[][] {
        let toCheck = RegionCreatorUtils.arrayDeepcopy(this.freeNeighbors[cellId]);
        let fields: number[][];
        fields = [];
        let currField: number[];
        currField = [];
        let neighborsInCurrentField = [];
        neighborsInCurrentField.push(toCheck[0]);
        let doContinue = true;
        let freeNeighbor: number;
        let neighborToCheck: number;
        while (doContinue) {
            if (neighborsInCurrentField.length === 0) {
                fields.push(currField);
                if (toCheck.length === 0) {
                    doContinue = false;
                    continue;
                }
                currField = [];
                neighborsInCurrentField.push(toCheck[0]);
            }
            neighborToCheck = neighborsInCurrentField[0];
            for (let i = 0; i < this.freeNeighbors[neighborToCheck].length; i++) {
                freeNeighbor = this.freeNeighbors[neighborToCheck][i];
                if (neighborsInCurrentField.indexOf(freeNeighbor) === -1 && currField.indexOf(freeNeighbor) === -1) {
                    neighborsInCurrentField.push(freeNeighbor);
                }
            }
            if (toCheck.indexOf(neighborToCheck) >= 0) {
                toCheck = RegionCreatorUtils.arrayRemoveOne(toCheck, neighborToCheck);
            }
            currField.push(neighborToCheck);
            neighborsInCurrentField.shift();
        }
        return fields;
    }

    private undoSeparateFields(addedFields: number[], prevFieldId: number): void {
        for (let i = 0; i < addedFields.length; i++) {
            let fieldId = addedFields[i];
            this.neighboringFields = RegionCreatorUtils.arrayRemoveOne(this.neighboringFields, fieldId);
            for (let j = 0; j < this.cellsForFields[fieldId].length; j++) {
                let cellId = this.cellsForFields[fieldId][j];
                this.fieldForCell[cellId] = prevFieldId;
                this.cellsForFields[prevFieldId].push(cellId);
            }
        }
        for (let i = 0; i < addedFields.length; i++) {
            this.cellsForFields.pop();
        }
        return;
    }

    private undoAddNewNeighbors(regionSize: number, cellsLeftToPlace: number, cellId: number, addedNeighbors: number[], prevFieldId: number): void {
        if (regionSize !== cellsLeftToPlace) {
            this.neighboringCells.push(cellId);
        }
        for (let i = 0; i < addedNeighbors.length; i++) {
            this.neighboringCells = RegionCreatorUtils.arrayRemoveOne(this.neighboringCells, addedNeighbors[i]);
        }
        if (regionSize === cellsLeftToPlace) {
            this.neighboringFields = RegionCreatorUtils.arrayRemoveOne(this.neighboringFields, prevFieldId);
        }
        return;
    }

    private undoPlaceCell(cellId: number, prevFieldId: number): void {
        this.regionForCell[cellId] = -1;
        this.fieldForCell[cellId] = prevFieldId;
        for (let i = 0; i < this.freeNeighbors[cellId].length; i++) {
            this.freeNeighbors[this.freeNeighbors[cellId][i]].push(cellId);
        }
        this.cellsForFields[prevFieldId].push(cellId);
        return;
    }

    // PACKABILITY
    // After a cell is placed, the free cells split into fields (connected groups of free cells).
    // Every "necessary" field (one the current region can't reach anymore) must be filled exactly
    // by the regions that are left; "optional" fields (next to the current region) may keep space
    // left over, because the current region can still grow into them.

    private checkPackability(regionSize: number, cellsLeftToPlace: number): boolean {
        let isPackable = true;
        if (this.neighboringFields.length > 1 || regionSize === cellsLeftToPlace) {
            let fieldSizes = [];
            for (let i = 0; i < this.cellsForFields.length; i++) {
                fieldSizes.push(this.cellsForFields[i].length);
            }
            let sizesToPack = [];
            for (let i = 0; i < this.regionSizesLeft.length; i++) {
                sizesToPack.push(this.regionSizesLeft[i]);
            }
            let optionalFields = RegionCreatorUtils.arrayDeepcopy(this.neighboringFields);
            isPackable = RegionCreator.getIsPackable(fieldSizes, sizesToPack, optionalFields);
        }
        return isPackable;
    }

    private static getIsPackable(fieldSizes: number[], sizesToPack: number[], optionalFields: number[]): boolean {
        let isOptional = new Set(optionalFields);
        let necessaryFields = [];
        for (let i = 0; i < fieldSizes.length; i++) {
            if ( !isOptional.has(i)) {
                necessaryFields.push(i);
            }
        }
        return RegionCreator.packNext({ fieldSizes, sizesToPack, necessaryFields, optionalFields });
    }

    // Takes all regions of the size at the end of sizesToPack and tries every way of splitting them
    // between the necessary and the optional fields, then continues with the next size.
    // fieldSizes and sizesToPack are restored when it returns false.
    private static packNext(packing: RegionCreatorPacking): boolean {
        let { fieldSizes, sizesToPack, necessaryFields, optionalFields } = packing;
        if (sizesToPack.length === 0) {
            return RegionCreatorUtils.arrayGetSumOnElements(fieldSizes, necessaryFields) === 0;
        }
        let size = sizesToPack[sizesToPack.length - 1];
        let count = 0;
        while (sizesToPack.length > 0 && sizesToPack[sizesToPack.length - 1] === size) {
            count += 1;
            sizesToPack.pop();
        }

        let necessary = RegionCreator.getFittableFields(fieldSizes, necessaryFields, size);
        let optional = RegionCreator.getFittableFields(fieldSizes, optionalFields, size);

        if (count <= necessary.space + optional.space) {
            let necessaryMin = Math.max(0, count - optional.space);
            let necessaryMax = Math.min(count, necessary.space);
            for (let necessaryCount = necessaryMin; necessaryCount <= necessaryMax; necessaryCount++) {
                let isPackable = RegionCreator.fillGroups(packing, size, necessary, 0, necessary.space, necessaryCount,
                    () => RegionCreator.fillGroups(packing, size, optional, 0, optional.space, count - necessaryCount,
                        () => RegionCreator.packNext(packing)
                    )
                );
                if (isPackable) {
                    return true;
                }
            }
        }

        for (let i = 0; i < count; i++) {
            sizesToPack.push(size);
        }
        return false;
    }

    // Decides how many of the toPlace regions go into each group of equally sized fields (from groupId on),
    // then calls next. spaceLeft is how many regions fit into the groups from groupId on.
    private static fillGroups(
        packing: RegionCreatorPacking, size: number, groups: RegionCreatorFieldGroups,
        groupId: number, spaceLeft: number, toPlace: number, next: () => boolean
    ): boolean {
        if (groupId === groups.sizes.length) {
            return next();
        }
        let fitsInField = Math.floor(groups.sizes[groupId] / size);
        let groupSpace = groups.fields[groupId].length * fitsInField;
        let minUse = Math.max(0, toPlace + groupSpace - spaceLeft);  // what the later groups can't take
        let maxUse = Math.min(groupSpace, toPlace);
        for (let use = minUse; use <= maxUse; use++) {
            let isPackable = RegionCreator.fillFields(packing, size, groups, groupId, spaceLeft - groupSpace, toPlace - use, next, 0, use, use);
            if (isPackable) {
                return true;
            }
        }
        return false;
    }

    // Spreads useLeft regions over the fields of one group (from fieldIndex on), then moves on to the next group.
    // The fields of a group are interchangeable, so each field gets at most as many regions as the one before it
    // (maxPerField), which skips permutations of the same split.
    private static fillFields(
        packing: RegionCreatorPacking, size: number, groups: RegionCreatorFieldGroups, groupId: number,
        spaceLeft: number, toPlace: number, next: () => boolean,
        fieldIndex: number, useLeft: number, maxPerField: number
    ): boolean {
        if (useLeft === 0) {
            return RegionCreator.fillGroups(packing, size, groups, groupId + 1, spaceLeft, toPlace, next);
        }
        let fields = groups.fields[groupId];
        let fitsInField = Math.floor(groups.sizes[groupId] / size);
        let fieldsLeft = fields.length - fieldIndex;
        for (let use = 1; use <= Math.min(useLeft, maxPerField, fitsInField); use++) {
            if (use * fieldsLeft < useLeft) {  // the remaining fields (each getting at most `use`) couldn't take the rest
                continue;
            }
            let fieldId = fields[fieldIndex];
            packing.fieldSizes[fieldId] -= size * use;
            let isPackable = RegionCreator.fillFields(packing, size, groups, groupId, spaceLeft, toPlace, next, fieldIndex + 1, useLeft - use, use);
            if (isPackable) {
                return true;
            }
            packing.fieldSizes[fieldId] += size * use;
        }
        return false;
    }

    // Groups the fields (from fromFields) that a region of the given size fits in by their size.
    private static getFittableFields(fieldSizes: number[], fromFields: number[], size: number): RegionCreatorFieldGroups {
        let groups: RegionCreatorFieldGroups = { sizes: [], fields: [], space: 0 };
        for (const field of fromFields) {
            let fieldSize = fieldSizes[field];
            if (fieldSize >= size) {
                let sizeIndex = groups.sizes.indexOf(fieldSize);
                if (sizeIndex === -1) {
                    sizeIndex = groups.sizes.length;
                    groups.sizes.push(fieldSize);
                    groups.fields.push([]);
                }
                groups.fields[sizeIndex].push(field);
                groups.space += Math.floor(fieldSize / size);
            }
        }
        return groups;
    }
}