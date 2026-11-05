import Sir

namespace SirTests.Safety

open Sir Host CoFree

def noop : Program where
  init := 0
  main := 1
  functions := #[
    {
      entry := 0,
      returns := .never,
      blocks := #[
        {
          ops := #[
            .let 0 .mainLength,
            .let 1 (.malloc 0),
            .let 2 .mainStartOffset,
            .stmt (.codecopy 1 2 0)
          ]
          control := .return 1 0
        }
      ]
    },
    {
      entry := 0,
      returns := .never,
      blocks := #[
        { control := .stop }
      ]
    }
  ]
  mainDatas := []

def initStops : Program where
  init := 0
  main := 1
  functions := #[
    { entry := 0, returns := .never, blocks := #[{ control := .stop }] },
    { entry := 0, returns := .never, blocks := #[{ control := .stop }] }]
  mainDatas := []

end SirTests.Safety
