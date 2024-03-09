/*

    1, 1, 2, 3, 5, 8, 13, ...

    | elem_1 | elem_2 | sum | q_fib
    --------------------------------
    |    1   |    1   |  2  |   1
    |    1   |    2   |  3  |   1
    |    2   |    3   |  5  |   1
    |        |        |     |   0

    q_fib * (elem_1 + elem_2 - elem_3) = 0

*/

// Halo2プルーフシステムとその他必要なクレートからの要素をインポート
use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::{AssignedCell, Layouter, Value};
use halo2_proofs::plonk::*;
use halo2_proofs::poly::Rotation;

// Config構造体を定義。これは、回路の構成を保持します。
#[derive(Clone, Debug, Copy)]
struct Config {
    elem_1: Column<Advice>,     // 最初のフィボナッチ数を格納するadvice column
    elem_2: Column<Advice>,     // 2番目のフィボナッチ数を格納するadvice column
    elem_3: Column<Advice>,     // 計算される数を格納するadvice column
    q_fib: Selector,            // 計算の適用を制御するselector
    instance: Column<Instance>, // public inputを格納するinstance column
}

impl Config {
    // Configのconfigureメソッドを定義。これは、回路の設定を行う
    fn configure<F: Field>(cs: &mut ConstraintSystem<F>) -> Self {
        // 可変のConstraintSystem参照を引数として受け取る
        // advice columnを作成し、それぞれに等価性の制約を有効にする
        let elem_1 = cs.advice_column();
        cs.enable_equality(elem_1);
        let elem_2 = cs.advice_column();
        cs.enable_equality(elem_2);
        let elem_3 = cs.advice_column();
        cs.enable_equality(elem_3);

        // instance columnを作成し、等価性の制約を有効にする
        let instance = cs.instance_column();
        cs.enable_equality(instance);

        // 計算の適用を制御するselectorを作成
        let q_fib = cs.selector();

        // フィボナッチ数列の計算を表すゲート（制約）を作成
        cs.create_gate("fibonacci", |virtual_cells| {
            // セレクタと各advice columnの現在の値を問い合わせる
            let q_fib = virtual_cells.query_selector(q_fib);
            let elem_1 = virtual_cells.query_advice(elem_1, Rotation::cur());
            let elem_2 = virtual_cells.query_advice(elem_2, Rotation::cur());
            let elem_3 = virtual_cells.query_advice(elem_3, Rotation::cur());

            // フィボナッチ数列の特定の性質を検証する制約を定義します。
            // elem_1 + elem_2 - elem_3 が0となるようにする　-> elem_3 = elem_1 + elem_2 を保証する
            vec![q_fib * (elem_1 + elem_2 - elem_3)]
        });

        // Config構造体のインスタンスを返す
        Self {
            elem_1,
            elem_2,
            elem_3,
            q_fib,
            instance,
        }
    }

    fn init<F: Field>(
        &self,
        mut layouter: impl Layouter<F>,
        elem_1: Value<F>,
        elem_2: Value<F>,
    ) -> Result<
        (
            AssignedCell<F, F>, // elem_2
            AssignedCell<F, F>, // elem_3
        ),
        Error,
    > {
        println!("elem_1: {:?}", elem_1);
        println!("elem_2: {:?}", elem_2);
        layouter.assign_region(
            || "init Fibonacci",
            |mut region| {
                let offset = 0;

                // Enable q_fib
                self.q_fib.enable(&mut region, offset)?;

                // Assign elem_1
                region.assign_advice(|| "elem_1", self.elem_1, offset, || elem_1)?;

                // Assign elem_2
                let elem_2 = region.assign_advice(|| "elem_2", self.elem_2, offset, || elem_2)?;
                // let elem_3 = elem_1;
                let elem_3 = elem_1 + elem_2.value_field().evaluate();
                // Assign elem_3
                let elem_3 = region.assign_advice(|| "elem_3", self.elem_3, offset, || elem_3)?;

                Ok((elem_2, elem_3))
            },
        )
    }

    fn assign<F: Field>(
        &self,
        mut layouter: impl Layouter<F>,
        elem_2: &AssignedCell<F, F>,
        elem_3: &AssignedCell<F, F>,
    ) -> Result<
        (
            AssignedCell<F, F>, // elem_2
            AssignedCell<F, F>, // elem_3
        ),
        Error,
    > {
        layouter.assign_region(
            || "next row",
            |mut region| {
                let offset = 0;

                // Enable q_fib
                self.q_fib.enable(&mut region, offset)?;

                // Copy elem_1 (which is the previous elem_2)
                let elem_1 = elem_2.copy_advice(
                    || "copy elem_2 into current elem_1",
                    &mut region,
                    self.elem_1,
                    offset,
                )?;

                // Copy elem_2 (which is the previous elem_3)
                let elem_2 = elem_3.copy_advice(
                    || "copy elem_3 into current elem_2",
                    &mut region,
                    self.elem_2,
                    offset,
                )?;
                let elem_3 = elem_1.value_field().evaluate() + elem_2.value_field().evaluate();
                //comment next line makes constaint not satified
                // let elem_3 = elem_1.value_field().evaluate() + elem_2.value_field().evaluate() + elem_2.value_field().evaluate();
                // Assign elem_3
                let elem_3 = region.assign_advice(|| "elem_3", self.elem_3, offset, || elem_3)?;

                Ok((elem_2, elem_3))
            },
        )
    }

    fn expose_public<F: Field>(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.instance, row)
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, pasta::Fp};

    use super::*;

    /*
        1, 1, 2, 3, 5, 8, 13, ...

        | elem_1 | elem_2 | sum | q_fib | instance
        --------------------------------
        |    1   |    1   |  2  |   1   | 55
        |    1   |    2   |  3  |   1
        |    2   |    3   |  5  |   1
        |        |        |     |   0



    */

    #[derive(Default)]

    struct MyCircuit<F: Field> {
        elem_1: Value<F>, // 1
        elem_2: Value<F>, // 1
    }

    impl<F: Field> Circuit<F> for MyCircuit<F> {
        type Config = Config;

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            Self::Config::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // elem_2 = 1, elem_3 = 2
            let (mut elem_2, mut elem_3) =
                config.init(layouter.namespace(|| "init"), self.elem_1, self.elem_2)?;

            // 1 + 2 = 3
            for _i in 3..10 {
                let (_, new_elem_3) =
                    config.assign(layouter.namespace(|| "next row"), &elem_2, &elem_3)?;

                elem_2 = elem_3;
                elem_3 = new_elem_3;
            }
            config.expose_public(layouter, &elem_3, 0)?;
            Ok(())
        }
    }

    #[test]
    fn test_fib() {
        let circuit = MyCircuit {
            elem_1: Value::known(Fp::one()),
            elem_2: Value::known(Fp::one()),
        };
        let instance = Fp::from(55);
        let mut public_input = vec![instance];
        let prover = MockProver::run(5, &circuit, vec![public_input]).unwrap();

        prover.assert_satisfied();
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn print_fibo() {
        use plotters::prelude::*;
        let root = BitMapBackend::new("fib-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit {
            elem_1: Value::known(Fp::one()),
            elem_2: Value::known(Fp::one()),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(5, &circuit, &root)
            .unwrap();

        let dot_string = halo2_proofs::dev::circuit_dot_graph(&circuit);
        print!("{}", dot_string);
    }
}
